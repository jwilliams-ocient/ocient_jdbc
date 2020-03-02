package com.ocient.jdbc;

import java.io.BufferedInputStream;
import java.io.BufferedOutputStream;
import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.Socket;
import java.nio.charset.StandardCharsets;
import java.sql.Array;
import java.sql.Blob;
import java.sql.CallableStatement;
import java.sql.Clob;
import java.sql.Connection;
import java.sql.DatabaseMetaData;
import java.sql.Driver;
import java.sql.NClob;
import java.sql.PreparedStatement;
import java.sql.ResultSet;
import java.sql.SQLClientInfoException;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.sql.SQLWarning;
import java.sql.SQLXML;
import java.sql.Savepoint;
import java.sql.Statement;
import java.sql.Struct;
import java.util.ArrayList;
import java.util.Map;
import java.util.Properties;
import java.util.StringTokenizer;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.Executor;
import java.util.concurrent.atomic.AtomicReference;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.spec.IvParameterSpec;
import javax.crypto.spec.SecretKeySpec;
import javax.crypto.spec.DHParameterSpec;
import javax.crypto.interfaces.DHPublicKey;
import java.security.spec.X509EncodedKeySpec;
import java.security.KeyFactory;
import java.security.PrivateKey;
import java.security.PublicKey;
import java.security.MessageDigest;
import java.security.KeyFactory;
import java.security.KeyPair;
import java.security.KeyPairGenerator;
import javax.crypto.KeyAgreement;
import javax.crypto.Mac;
import java.util.Base64;
import com.google.protobuf.ByteString;
import com.ocient.jdbc.proto.ClientWireProtocol;
import com.ocient.jdbc.proto.ClientWireProtocol.ClientConnection;
import com.ocient.jdbc.proto.ClientWireProtocol.CloseConnection;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse.ResponseType;
import com.ocient.jdbc.proto.ClientWireProtocol.GetSchema;
import com.ocient.jdbc.proto.ClientWireProtocol.Request;
import com.ocient.jdbc.proto.ClientWireProtocol.SetSchema;
import com.ocient.jdbc.proto.ClientWireProtocol.ForceExternal;
import com.ocient.jdbc.proto.ClientWireProtocol.SetPSO;
import com.ocient.jdbc.proto.ClientWireProtocol.TestConnection;

public class XGConnection implements Connection
{
	private class TestConnectionThread extends Thread
	{
		Exception e = null;

		@Override
		public void run() {
			try
			{
				// send request
				final ClientWireProtocol.TestConnection.Builder builder =
						ClientWireProtocol.TestConnection.newBuilder();
				final TestConnection msg = builder.build();
				final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
				b2.setType(ClientWireProtocol.Request.RequestType.TEST_CONNECTION);
				b2.setTestConnection(msg);
				final Request wrapper = b2.build();

				try
				{
					out.write(intToBytes(wrapper.getSerializedSize()));
					wrapper.writeTo(out);
					out.flush();
					getStandardResponse();
				}
				catch (SQLException | IOException e)
				{
					if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e))
					{
						throw e;
					}

					reconnect();
					run();
					return;
				}
			}
			catch (final Exception e)
			{
				this.e = e;
			}
		}
	}

	private static int bytesToInt(final byte[] val) {
		final int ret = java.nio.ByteBuffer.wrap(val).getInt();
		return ret;
	}

	private static byte[] intToBytes(final int val) {
		final byte[] buff = new byte[4];
		buff[0] = (byte) (val >> 24);
		buff[1] = (byte) ((val & 0x00FF0000) >> 16);
		buff[2] = (byte) ((val & 0x0000FF00) >> 8);
		buff[3] = (byte) ((val & 0x000000FF));
		return buff;
	}

	protected BufferedInputStream in;
	protected BufferedOutputStream out;
	private boolean closed = false;
	private boolean connected = true;
	private Socket sock;
	protected XGResultSet rs;
	protected int portNum;
	protected ArrayList<SQLWarning> warnings = new ArrayList<>();
	protected String url;
	protected String user;
	protected String database;
	protected String client = "jdbc";
	protected String version;
	protected String setSchema = "";
	protected long setPso = 0;
	protected boolean force = false;
	private volatile long timeoutMillis = 0L; // 0L means no timeout set

	protected boolean oneShotForce = false;
	protected ArrayList<String> cmdcomps = new ArrayList<>();

	// The timer is initially null, created when the first query timeout is set and destroyed on close()
	private final AtomicReference<Timer> timer = new AtomicReference<>();

	protected String pwd;
	private int retryCounter;

	public XGConnection(final Socket sock, final String user, final String pwd, final int portNum, final String url,
			final String database, final String version, final String force) throws Exception
	{
		if (force.equals("true"))
		{
			this.force = true;
		}

		this.url = url;
		this.user = user;
		this.pwd = pwd;
		this.sock = sock;
		this.portNum = portNum;
		this.database = database;
		this.version = version;
		this.retryCounter = 0;
		in = new BufferedInputStream(sock.getInputStream());
		out = new BufferedOutputStream(sock.getOutputStream());
		try
		{

			clientHandshake(user, pwd, database);
		}
		catch (final Exception e)
		{
			e.printStackTrace();
			throw e;
		}
	}

	@Override
	public void abort(final Executor executor) throws SQLException {
		if (executor == null)
		{
			throw SQLStates.INVALID_ARGUMENT.clone();
		}

		if (closed)
		{
			return;
		}

		this.close();
	}

	public void clearOneShotForce() {
		oneShotForce = false;
	}

	@Override
	public void clearWarnings() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		warnings.clear();
	}

	/*!
	 * This timeout will be applied to every XGStatement created
	 */
	public void setTimeout(final int seconds) throws SQLException {
		if (seconds < 0) {
			throw new SQLWarning(String.format("timeout value must be non-negative, was: %s", seconds));
		}
		this.timeoutMillis = seconds * 1000;
	}

	protected long getTimeoutMillis() {
		return timeoutMillis;
	}

	/**
	 * Creates a new {@link Timer} or returns the existing one if it already exists
	 */
	private Timer getTimer() {
		return this.timer.updateAndGet(existing -> existing != null ? existing : new Timer());
	}

	/**
	 * Schedules the task to run after the specified delay
	 * 
	 * @param task the task to run
	 * @param timeout delay in milliseconds
	 */
	protected void addTimeout(final TimerTask task, final long timeout) {
		getTimer().schedule(task, timeout);
	}

	/**
	 * Purges all canceled tasks from the timer.
	 * 
	 * Note: You should only call this if you've canceled a timer. This call may create a {@link Timer} 
	 * object if one does not already exist
	 */
	protected void purgeTimeoutTasks() {
		getTimer().purge();
	}

	private void clientHandshake(final String userid, final String pwd, final String db) throws Exception {
		try
		{
			// send first part of handshake - contains userid
			final ClientWireProtocol.ClientConnection.Builder builder =
					ClientWireProtocol.ClientConnection.newBuilder();
			builder.setUserid(userid);
			builder.setDatabase(database);
			builder.setClientid(client);
			builder.setVersion(version);
			final ClientConnection msg = builder.build();
			ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
			b2.setType(ClientWireProtocol.Request.RequestType.CLIENT_CONNECTION);
			b2.setClientConnection(msg);
			Request wrapper = b2.build();
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();

			// get response
			final ClientWireProtocol.ClientConnectionResponse.Builder ccr =
					ClientWireProtocol.ClientConnectionResponse.newBuilder();
			int length = getLength();
			byte[] data = new byte[length];
			readBytes(data);
			ccr.mergeFrom(data);
			ConfirmationResponse response = ccr.getResponse();
			ResponseType rType = response.getType();
			processResponseType(rType, response);
			final ByteString ivString = ccr.getIv();
         byte[] key = new byte[256];
         byte[] macKey = new byte[256];
         String myPubKey;

         try {
            String keySpec = ccr.getPubKey();
            keySpec = keySpec.replace("-----BEGIN PUBLIC KEY-----\n", "");
            keySpec = keySpec.replace("-----END PUBLIC KEY-----\n", "");
            byte[] keyBytes = Base64.getMimeDecoder().decode(keySpec.getBytes(StandardCharsets.UTF_8));
            X509EncodedKeySpec x509keySpec = new X509EncodedKeySpec(keyBytes);
            KeyFactory keyFact = KeyFactory.getInstance("DH");
            DHPublicKey pubKey = (DHPublicKey)keyFact.generatePublic(x509keySpec);
            DHParameterSpec params =  pubKey.getParams();

            KeyPairGenerator keyGen = KeyPairGenerator.getInstance("DH");
            keyGen.initialize(params);
            KeyPair kp = keyGen.generateKeyPair();

            KeyAgreement ka = KeyAgreement.getInstance("DiffieHellman");
            ka.init(kp.getPrivate());
            ka.doPhase(pubKey, true);
            byte[] secret = ka.generateSecret();

            byte [] buffer = new byte[5 + secret.length];
            buffer[0] = (byte) ((secret.length & 0xff000000) >> 24);
            buffer[1] = (byte) ((secret.length & 0xff0000) >> 16);
            buffer[2] = (byte) ((secret.length & 0xff00) >> 8);
            buffer[3] = (byte) (secret.length & 0xff);
            System.arraycopy(secret, 0, buffer, 5, secret.length);

            buffer[4] = 0x00;
            MessageDigest sha = MessageDigest.getInstance("SHA-256");
            key = sha.digest(buffer);

            buffer[4] = 0x01;
            sha = MessageDigest.getInstance("SHA-256");
            macKey = sha.digest(buffer);

            PublicKey clientPub = kp.getPublic();
            myPubKey = "-----BEGIN PUBLIC KEY-----\n" + 
               Base64.getMimeEncoder().encodeToString(clientPub.getEncoded()) + "\n-----END PUBLIC KEY-----\n";
         }
         catch(Exception e) {
            throw new Exception(e);
         }

         final byte[] iv = ivString.toByteArray();
			final IvParameterSpec ips = new IvParameterSpec(iv);

			// Create a key specification first, based on our key input.
			final SecretKey aesKey = new SecretKeySpec(key, "AES");
         final SecretKey hmacKey = new SecretKeySpec(macKey, "AES");

			// Create a Cipher for encrypting the data using the key we created.
			Cipher encryptCipher;

			encryptCipher = Cipher.getInstance("AES/CBC/PKCS5Padding");
			// Initialize the Cipher with key and parameters
			encryptCipher.init(Cipher.ENCRYPT_MODE, aesKey, ips);

			// Our cleartext
			final byte[] cleartext = pwd.getBytes(StandardCharsets.UTF_8);

			// Encrypt the cleartext
			final byte[] ciphertext = encryptCipher.doFinal(cleartext);

         Mac hmac = Mac.getInstance("HmacSha256");
         hmac.init(hmacKey);
         final byte[] calculatedMac = hmac.doFinal(ciphertext);

			// send handshake part2
			final ClientWireProtocol.ClientConnection2.Builder hand2 =
					ClientWireProtocol.ClientConnection2.newBuilder();
			hand2.setCipher(ByteString.copyFrom(ciphertext));
         hand2.setPubKey(myPubKey);
         hand2.setHmac(ByteString.copyFrom(calculatedMac));
			if (force)
			{
				hand2.setForce(true);
			}
			else if (oneShotForce)
			{
				oneShotForce = false;
				hand2.setForce(true);
			}
			else
			{
				hand2.setForce(false);
			}
			final ClientWireProtocol.ClientConnection2 msg2 = hand2.build();
			b2 = ClientWireProtocol.Request.newBuilder();
			b2.setType(ClientWireProtocol.Request.RequestType.CLIENT_CONNECTION2);
			b2.setClientConnection2(msg2);
			wrapper = b2.build();
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();

			// getResponse
			final ClientWireProtocol.ClientConnection2Response.Builder ccr2 =
					ClientWireProtocol.ClientConnection2Response.newBuilder();
			length = getLength();
			data = new byte[length];
			readBytes(data);
			ccr2.mergeFrom(data);
			response = ccr2.getResponse();
			rType = response.getType();
			
			SQLException state = new SQLException(response.getReason(), response.getSqlState(), response.getVendorCode());
			//if we had a failed handshake, then something went wrong with verification on the server, just try again(up to 5 times)
			if(SQLStates.FAILED_HANDSHAKE.equals(state) && retryCounter++ < 5) {
				clientHandshake(userid, pwd, db);
				return;
			}
			retryCounter = 0;
			processResponseType(rType, response);
			if (ccr2.getRedirect())
			{
				final String host = ccr2.getRedirectHost();
				final int port = ccr2.getRedirectPort();
				redirect(host, port);
			}
			else
			{
				final int count = ccr2.getCmdcompsCount();
				cmdcomps.clear();
				for (int i = 0; i < count; i++)
				{
					cmdcomps.add(ccr2.getCmdcomps(i));
				}
			}
		}
		catch (final Exception e)
		{
			e.printStackTrace();
			
			try
			{
				sock.close();
			}
			catch (final Exception f)
			{}

			throw e;
		}
	}

	@Override
	public void close() throws SQLException {
		if (closed)
		{
			return;
		}

		closed = true;
		try
		{
			sendClose();
		}
		catch (final Exception e)
		{}

		try
		{
			in.close();
			out.close();
			sock.close();
		}
		catch (final Exception e)
		{}

		// Cleanup our timer, if one exists
		Timer t = null;
		do {
			t = timer.get();
			if (t == null) {
				return;
			}
		} while (!timer.compareAndSet(t, null));
		t.cancel();
	}

	@Override
	public void commit() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		// !!!!!!!!!!!!!! NO-OP !!!!!!!!!!!!!!!!!!!
	}

	@Override
	public Array createArrayOf(final String arg0, final Object[] arg1) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public Blob createBlob() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public Clob createClob() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public NClob createNClob() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public SQLXML createSQLXML() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public Statement createStatement() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // The statement inherits our one shot
			return new XGStatement(this, force, true);
		}
		else
		{
			return new XGStatement(this, force, false);
		}
	}

	@Override
	public Statement createStatement(final int arg0, final int arg1) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // Statement inherits our one shot
			return new XGStatement(this, arg0, arg1, force, true);
		}
		else
		{
			return new XGStatement(this, arg0, arg1, force, false);
		}
	}

	@Override
	public Statement createStatement(final int arg0, final int arg1, final int arg2) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // Statement inherits our one shot
			return new XGStatement(this, arg0, arg1, arg2, force, true);
		}
		else
		{
			return new XGStatement(this, arg0, arg1, arg2, force, false);
		}
	}

	@Override
	public Struct createStruct(final String arg0, final Object[] arg1) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean getAutoCommit() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		return true;
	}

	@Override
	public String getCatalog() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		return null;
	}

	@Override
	public Properties getClientInfo() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return new Properties();
	}

	@Override
	public String getClientInfo(final String arg0) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return null;
	}

	public String getDB() {
		return database;
	}

	@Override
	public int getHoldability() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.CLOSE_CURSORS_AT_COMMIT;
	}

	private int getLength() throws Exception {
		final byte[] inMsg = new byte[4];

		int count = 0;
		while (count < 4)
		{
			final int temp = in.read(inMsg, count, 4 - count);
			if (temp == -1)
			{
				throw new IOException();
			}

			count += temp;
		}

		return bytesToInt(inMsg);
	}

	public int getMajorVersion() {
		return Integer.parseInt(version.substring(0, version.indexOf(".")));
	}

	@Override
	public DatabaseMetaData getMetaData() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return new XGDatabaseMetaData(this);
	}

	public int getMinorVersion() {
		final int i = version.indexOf(".") + 1;
		return Integer.parseInt(version.substring(i, version.indexOf(".", i)));
	}

	@Override
	public int getNetworkTimeout() throws SQLException {
		return 0;
	}

	@Override
	public String getSchema() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		try
		{
			return getSchemaFromServer();
		}
		catch (final Exception e)
		{
			if (e instanceof SQLException)
			{
				throw (SQLException) e;
			}
			else
			{
				throw SQLStates.newGenericException(e);
			}
		}
	}

	private String getSchemaFromServer() throws Exception {
		// send request
		final ClientWireProtocol.GetSchema.Builder builder = ClientWireProtocol.GetSchema.newBuilder();
		final GetSchema msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.GET_SCHEMA);
		b2.setGetSchema(msg);
		final Request wrapper = b2.build();

		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
		}
		catch (final IOException e)
		{
			if (!setSchema.equals(""))
			{
				return setSchema;
			}
			else
			{
				reconnect();
				return getSchemaFromServer();
			}
		}

		// get response
		final ClientWireProtocol.GetSchemaResponse.Builder gsr = ClientWireProtocol.GetSchemaResponse.newBuilder();

		try
		{
			final int length = getLength();
			final byte[] data = new byte[length];
			readBytes(data);
			gsr.mergeFrom(data);
		}
		catch (SQLException | IOException e)
		{
			if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e))
			{
				throw e;
			}

			if (!setSchema.equals(""))
			{
				return setSchema;
			}
			else
			{
				reconnect();
				return getSchemaFromServer();
			}
		}

		final ConfirmationResponse response = gsr.getResponse();
		final ResponseType rType = response.getType();
		processResponseType(rType, response);
		return gsr.getSchema();
	}

	private void getStandardResponse() throws Exception {
		final int length = getLength();
		final byte[] data = new byte[length];
		readBytes(data);
		final ConfirmationResponse.Builder rBuild = ConfirmationResponse.newBuilder();
		rBuild.mergeFrom(data);
		final ResponseType rType = rBuild.getType();
		processResponseType(rType, rBuild.build());
	}

	@Override
	public int getTransactionIsolation() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return Connection.TRANSACTION_NONE;
	}

	@Override
	public Map<String, Class<?>> getTypeMap() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	public String getURL() {
		return url;
	}

	public String getUser() {
		return user;
	}

	public String getVersion() {
		return version;
	}

	@Override
	public SQLWarning getWarnings() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (warnings.size() == 0)
		{
			return null;
		}

		final SQLWarning retval = warnings.get(0);
		SQLWarning current = retval;
		int i = 1;
		while (i < warnings.size())
		{
			current.setNextWarning(warnings.get(i));
			current = warnings.get(i);
			i++;
		}

		return retval;
	}

	@Override
	public boolean isClosed() throws SQLException {
		return closed;
	}

	@Override
	public boolean isReadOnly() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return false;
	}

	@Override
	public boolean isValid(final int arg0) throws SQLException {
		if (arg0 < 0)
		{
			throw SQLStates.INVALID_ARGUMENT.clone();
		}

		if (closed)
		{
			return false;
		}

		return testConnection(arg0);
	}

	@Override
	public boolean isWrapperFor(final Class<?> iface) throws SQLException {
		return false;
	}

	@Override
	public String nativeSQL(final String arg0) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return arg0;
	}

	@Override
	public CallableStatement prepareCall(final String arg0) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public CallableStatement prepareCall(final String arg0, final int arg1, final int arg2) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public CallableStatement prepareCall(final String arg0, final int arg1, final int arg2, final int arg3)
			throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // Statement inherits our one shot
			return new XGPreparedStatement(this, arg0, force, true);
		}
		else
		{
			return new XGPreparedStatement(this, arg0, force, false);
		}
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0, final int arg1) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0, final int arg1, final int arg2) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // Statement inherits our one shot
			return new XGPreparedStatement(this, arg0, arg1, arg2, force, true);
		}
		else
		{
			return new XGPreparedStatement(this, arg0, arg1, arg2, force, false);
		}
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0, final int arg1, final int arg2, final int arg3)
			throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (oneShotForce)
		{
			oneShotForce = false; // Statement inherits our one shot
			return new XGPreparedStatement(this, arg0, arg1, arg2, arg3, force, true);
		}
		else
		{
			return new XGPreparedStatement(this, arg0, arg1, arg2, arg3, force, false);
		}
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0, final int[] arg1) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public PreparedStatement prepareStatement(final String arg0, final String[] arg1) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	private void processResponseType(final ResponseType rType, final ConfirmationResponse response)
			throws SQLException {
		if (rType.equals(ResponseType.INVALID))
		{
			throw SQLStates.INVALID_RESPONSE_TYPE.clone();
		}
		else if (rType.equals(ResponseType.RESPONSE_ERROR))
		{
			final String reason = response.getReason();
			final String sqlState = response.getSqlState();
			final int code = response.getVendorCode();
			throw new SQLException(reason, sqlState, code);
		}
		else if (rType.equals(ResponseType.RESPONSE_WARN))
		{
			final String reason = response.getReason();
			final String sqlState = response.getSqlState();
			final int code = response.getVendorCode();
			warnings.add(new SQLWarning(reason, sqlState, code));
		}
	}

	private void readBytes(final byte[] data) throws Exception {
		final int z = data.length;
		int count = 0;
		while (count < z)
		{
			final int temp = in.read(data, count, z - count);
			if (temp == -1)
			{
				throw new IOException();
			}

			count += temp;
		}

		return;
	}

	/*
	 * Is the connection currently connected?
	 */
	public boolean connected() {
		return connected;
	}

	/*
	 * We seem to have lost our connection. Reconnect to any cmdcomp
	 */
	public void reconnect() throws IOException, SQLException {
		// Try to find any cmdcomp that we can connect to
		// If we can't connect to any throw IOException

		// There's any issue here that we don't want to force
		// But we could get redirected back to the dead node
		// Until the heartbeat timeout happens
		// Which could be up to 30 seconds
		// If the redirect fails, it will call reconnect
		// And we will end up looping until the heartbeat times out
		// In 30 seconds, we would totally blow out the stack

		// Even forcing, it only guarantees the first request after reconnect
		// is forced, which if the client is making a fast series of short
		// requests, puts us in the same situation

		// We solve this by delaying slightly, which will slow the rate
		// of stack growth enough that we will be ok
		try
		{
			Thread.sleep(250);
		}
		catch (final InterruptedException e)
		{}

		try
		{
			in.close();
			out.close();
			sock.close();
		}
		catch (final IOException e)
		{}
		
		if (force)
		{
			sock = null;
			try
			{
				sock = new Socket();
				sock.setReceiveBufferSize(4194304);
				sock.setSendBufferSize(4194304);
				sock.connect(new InetSocketAddress(this.url, this.portNum));
			}
			catch (final Exception e)
			{
				try
				{
					sock.close();
				}
				catch (final IOException f)
				{}

				// reconnect failed so we are no longer connected
				connected = false;
				
				if(e instanceof IOException) {
					throw (IOException)e;
				}
				
				throw new IOException();
			}

			try
			{
				in = new BufferedInputStream(sock.getInputStream());
				out = new BufferedOutputStream(sock.getOutputStream());

				clientHandshake(user, pwd, database);
				if (!setSchema.equals(""))
				{
					setSchema(setSchema);
				}
				
				if (setPso == -1)
				{
					//We have to turn it off
					setPSO(false);
				}
				else if (setPso > 0)
				{
					//Set non-default threshold
					setPSO(setPso);
				}

				return;
			}
			catch (final Exception handshakeException)
			{
				try
				{
					in.close();
					out.close();
					sock.close();
				}
				catch (final IOException f)
				{}
				
				// reconnect failed so we are no longer connected
				connected = false;
				
				// Failed on the client handshake, so capture exception
				if(handshakeException instanceof SQLException) {
					throw (SQLException) handshakeException;
				}
				
				throw new IOException();
			}
		}

		// capture any exception from trying to connect
		SQLException retVal = null;
		for (final String cmdcomp : cmdcomps)
		{
			final StringTokenizer tokens = new StringTokenizer(cmdcomp, ":", false);
			final String host = tokens.nextToken();
			final int port = Integer.parseInt(tokens.nextToken());

			// Try to connect to this one
			this.url = host;

			sock = null;
			try
			{
				sock = new Socket();
				sock.setReceiveBufferSize(4194304);
				sock.setSendBufferSize(4194304);
				sock.connect(new InetSocketAddress(host, port));
			}
			catch (final Exception e)
			{
				try
				{
					sock.close();
				}
				catch (final IOException f)
				{}

				continue;
			}

			this.portNum = port;
			try
			{
				in = new BufferedInputStream(sock.getInputStream());
				out = new BufferedOutputStream(sock.getOutputStream());

				clientHandshake(user, pwd, database);
				if (!setSchema.equals(""))
				{
					setSchema(setSchema);
				}
				
				if (setPso == -1)
				{
					//We have to turn it off
					setPSO(false);
				}
				else if (setPso > 0)
				{
					//Set non-default threshold
					setPSO(setPso);
				}

				return;
			}
			catch (final Exception handshakeException)
			{
				try
				{
					in.close();
					out.close();
					sock.close();
				}
				catch (final IOException f)
				{}
				// Failed on the client handshake, so capture exception
				if(handshakeException instanceof SQLException) {
					retVal = (SQLException) handshakeException;
				}
			}
			// reconnect failed so we are no longer connected
			connected = false;
		}

		// One of the cmdComps failed on handshake, so throw that exception
		if(retVal != null) {
			throw retVal;
		}
		throw new IOException();
	}

	/*
	 * We have to told to redirect our request elsewhere.
	 */
	public void redirect(final String host, final int port) throws IOException, SQLException {
		oneShotForce = true;

		// Close current connection
		try
		{
			in.close();
			out.close();
			sock.close();
		}
		catch (final IOException e)
		{}

		this.url = host;

		sock = null;
		try
		{
			sock = new Socket();
			sock.setReceiveBufferSize(4194304);
			sock.setSendBufferSize(4194304);
			sock.connect(new InetSocketAddress(host, port));
		}
		catch (final Exception e)
		{
			try
			{
				sock.close();
			}
			catch (final IOException f)
			{}

			reconnect();
			return;
		}

		this.portNum = port;

		try
		{
			in = new BufferedInputStream(sock.getInputStream());
			out = new BufferedOutputStream(sock.getOutputStream());
			clientHandshake(user, pwd, database);
			oneShotForce = true;
			if (!setSchema.equals(""))
			{
				setSchema(setSchema);
			}
			
			if (setPso == -1)
			{
				//We have to turn it off
				setPSO(false);
			}
			else if (setPso > 0)
			{
				//Set non-default threshold
				setPSO(setPso);
			}

			return;
		}
		catch (final Exception e)
		{
			try
			{
				in.close();
				out.close();
				sock.close();
			}
			catch (final IOException f)
			{}

			reconnect();
		}
	}

	@Override
	public void releaseSavepoint(final Savepoint arg0) throws SQLException {
		throw new SQLFeatureNotSupportedException();

	}

	@Override
	public void rollback() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void rollback(final Savepoint arg0) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	private void sendClose() throws Exception {
		// send request
		final ClientWireProtocol.CloseConnection.Builder builder = ClientWireProtocol.CloseConnection.newBuilder();
		final CloseConnection msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.CLOSE_CONNECTION);
		b2.setCloseConnection(msg);
		final Request wrapper = b2.build();

		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
		}
		catch (final IOException e)
		{
			// Who cares...
		}
	}

	private void sendSetSchema(final String schema) throws Exception {
		// send request
		final ClientWireProtocol.SetSchema.Builder builder = ClientWireProtocol.SetSchema.newBuilder();
		builder.setSchema(schema);
		final SetSchema msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.SET_SCHEMA);
		b2.setSetSchema(msg);
		final Request wrapper = b2.build();

		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
			getStandardResponse();
		}
		catch (final IOException e)
		{
			// Doesn't matter...
		}

		setSchema = schema;
	}
	
	public void forceExternal(boolean force) throws Exception {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		
		//send request
		final ClientWireProtocol.ForceExternal.Builder builder = ClientWireProtocol.ForceExternal.newBuilder();
		builder.setForce(force);
		final ForceExternal msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.FORCE_EXTERNAL);
		b2.setForceExternal(msg);
		final Request wrapper = b2.build();

		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
			getStandardResponse();
		}
		catch (final IOException e)
		{
			// Doesn't matter...
		}
	}
	
	//sets the pso threshold on this connection to threshold
	public void setPSO(long threshold) throws Exception {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
			
		//send request
		setPso = threshold;
		final ClientWireProtocol.SetPSO.Builder builder = ClientWireProtocol.SetPSO.newBuilder();
		builder.setThreshold(threshold);
		builder.setReset(false);
		final SetPSO msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.SET_PSO);
		b2.setSetPso(msg);
		final Request wrapper = b2.build();
	
		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
			getStandardResponse();
		}
		catch (final IOException e)
		{
			// Doesn't matter...
		}
	}
	
	//sets the pso threshold on this connection to be -1(meaning pso is turned off) or back to the default
	public void setPSO(boolean on) throws Exception {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		
		if (on)
		{
			setPso = 0;
		}
		else
		{
			setPso = -1;
		}
		
		//send request
		final ClientWireProtocol.SetPSO.Builder builder = ClientWireProtocol.SetPSO.newBuilder();
		builder.setThreshold(-1);
		builder.setReset(on);
		final SetPSO msg = builder.build();
		final ClientWireProtocol.Request.Builder b2 = ClientWireProtocol.Request.newBuilder();
		b2.setType(ClientWireProtocol.Request.RequestType.SET_PSO);
		b2.setSetPso(msg);
		final Request wrapper = b2.build();
	
		try
		{
			out.write(intToBytes(wrapper.getSerializedSize()));
			wrapper.writeTo(out);
			out.flush();
			getStandardResponse();
		}
		catch (final IOException e)
		{
			// Doesn't matter...
		}
	}

	@Override
	public void setAutoCommit(final boolean arg0) throws SQLException {}

	@Override
	public void setCatalog(final String arg0) throws SQLException {}

	@Override
	public void setClientInfo(final Properties arg0) throws SQLClientInfoException {}

	@Override
	public void setClientInfo(final String arg0, final String arg1) throws SQLClientInfoException {}

	@Override
	public void setHoldability(final int arg0) throws SQLException {
		if (arg0 != ResultSet.CLOSE_CURSORS_AT_COMMIT)
		{
			throw new SQLFeatureNotSupportedException();
		}
	}

	@Override
	public void setNetworkTimeout(final Executor executor, final int milliseconds) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setReadOnly(final boolean arg0) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
	}

	@Override
	public Savepoint setSavepoint() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public Savepoint setSavepoint(final String arg0) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setSchema(final String schema) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		try
		{
			sendSetSchema(schema);
		}
		catch (final Exception e)
		{
			if (e instanceof SQLException)
			{
				throw (SQLException) e;
			}
			else
			{
				throw SQLStates.newGenericException(e);
			}
		}
	}

	@Override
	public void setTransactionIsolation(final int arg0) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (arg0 != Connection.TRANSACTION_NONE)
		{
			throw new SQLFeatureNotSupportedException();
		}
	}

	@Override
	public void setTypeMap(final Map<String, Class<?>> arg0) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	private boolean testConnection(final int timeoutSecs) {
		final TestConnectionThread thread = new TestConnectionThread();
		thread.start();
		try
		{
			thread.join(timeoutSecs * 1000);
		}
		catch (final Exception e)
		{}

		if (thread.isAlive())
		{
			return false;
		}

		if (thread.e != null)
		{
			return false;
		}

		return true;
	}

	@Override
	public <T> T unwrap(final Class<T> iface) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}
}
