package com.ocient.jdbc;

import java.io.IOException;
import java.lang.reflect.Method;
import java.sql.Connection;
import java.sql.Date;
import java.sql.ResultSet;
import java.sql.SQLException;
import java.sql.SQLFeatureNotSupportedException;
import java.sql.SQLTimeoutException;
import java.sql.SQLWarning;
import java.sql.Statement;
import java.sql.Timestamp;
import java.sql.Time;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Optional;
import java.util.OptionalLong;
import java.util.logging.Logger;
import java.util.logging.FileHandler;
import java.util.logging.Level;
import com.ocient.jdbc.proto.ClientWireProtocol;
import com.ocient.jdbc.proto.ClientWireProtocol.CancelQuery;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse;
import com.ocient.jdbc.proto.ClientWireProtocol.ConfirmationResponse.ResponseType;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExplain;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExplainForSpark;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExplainForSpark.PartitioningType;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExport;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteExportResponse;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecutePlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteInlinePlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteQuery;
import com.ocient.jdbc.proto.ClientWireProtocol.ExecuteUpdate;
import com.ocient.jdbc.proto.ClientWireProtocol.ExplainPlan;
import com.ocient.jdbc.proto.ClientWireProtocol.ListPlan;
import com.ocient.jdbc.proto.ClientWireProtocol.FetchSystemMetadata;
import com.ocient.jdbc.proto.ClientWireProtocol.Request;
import com.ocient.jdbc.proto.ClientWireProtocol.SysQueriesRow;
import com.ocient.jdbc.proto.PlanProtocol.PlanMessage;
import com.ocient.jdbc.proto.ClientWireProtocol.SystemWideQueries;
import com.ocient.jdbc.proto.ClientWireProtocol.KillQuery;
import java.util.TimeZone;
import java.util.Timer;
import java.util.TimerTask;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.Executors;

import com.google.common.base.Preconditions;
import com.google.protobuf.util.JsonFormat;

public class XGStatement implements Statement
{
	private static final Logger LOGGER = Logger.getLogger( "com.ocient.jdbc" );

	private static final int defaultFetchSize = 30000;

	private static String bytesToHex(final byte[] in) {
		final StringBuilder builder = new StringBuilder();
		for (final byte b : in)
		{
			builder.append(String.format("%02x", b));
		}
		return builder.toString();
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

	protected boolean closed = false;
	private final XGConnection conn;
	private XGResultSet result;
	private int updateCount = -1;
	private int fetchSize = defaultFetchSize;
	protected ArrayList<Object> parms = new ArrayList<>();
	private int maxRows = 0;

	// not thread safe because individual queries are single threaded
	// The queryId is set on the initial call to executeQuery()
	// TODO enable timeouts on initial call to executeQuery()
	private String queryId = null;

	private final ArrayList<SQLWarning> warnings = new ArrayList<>();

	private final boolean force;

	// the tmeout is inherited from the connection but can be updated
	// via setQueryTimeout()
	private volatile long timeoutMillis;

	private boolean oneShotForce;

	public XGStatement(final XGConnection conn, final boolean force, final boolean oneShotForce)
	{
		this.conn = conn;
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout
	}

	public XGStatement(final XGConnection conn, final int type, final int concur, final boolean force,
			final boolean oneShotForce) throws SQLFeatureNotSupportedException
	{
		this.conn = conn;
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout
		if (concur != ResultSet.CONCUR_READ_ONLY)
		{
			throw new SQLFeatureNotSupportedException();
		}

		if (type != ResultSet.TYPE_FORWARD_ONLY)
		{
			throw new SQLFeatureNotSupportedException();
		}
	}

	public XGStatement(final XGConnection conn, final int type, final int concur, final int hold, final boolean force,
			final boolean oneShotForce) throws SQLFeatureNotSupportedException
	{
		this.conn = conn;
		this.force = force;
		this.oneShotForce = oneShotForce;
		this.timeoutMillis = conn.getTimeoutMillis(); // inherit the connections timeout

		if (concur != ResultSet.CONCUR_READ_ONLY)
		{
			throw new SQLFeatureNotSupportedException();
		}

		if (type != ResultSet.TYPE_FORWARD_ONLY)
		{
			throw new SQLFeatureNotSupportedException();
		}

		if (type != ResultSet.CLOSE_CURSORS_AT_COMMIT)
		{
			throw new SQLFeatureNotSupportedException();
		}
	}

	/**
	 * Associates the query with this statement
	 */
	private void associateQuery(final String queryId) {
		assert this.queryId == null : "Statement was not cleaned up before next query was dispatched";
		this.queryId = queryId;
	}

	/**
	 * Dissociate the current query with this statement
	 */
	private void dissociateQuery() {
		this.queryId = null;
	}

	protected Optional<String> getQueryId() {
		return Optional.ofNullable(queryId).filter(s -> !s.isEmpty());
	}

	/**
	 * Same as {@link Runnable} but can throw an exception
	 */
	protected interface ExceptionalRunnable {
		void run() throws Exception;
	}

	/**
	 * Executes a potentially exceptional task, canceling the backing query its it takes longer 
	 * than the timeout specified by {@link #getQueryTimeout()}.
	 * 
	 * @param task 				the task to execute
	 * @param optQueryId 		the query associated with this task. Empty of none exists
	 * @param timeoutMillis		the number of milliseconds to wait before firing off a kill query
	 * 							command to the sql node
	 * 
	 * @throws SQLTimeoutException if the timeout is reached before the call completes
	 */
	protected void startTask(ExceptionalRunnable task, final Optional<String> optQueryId, final long timeoutMillis) throws Exception {
		Preconditions.checkArgument(timeoutMillis >= 0L);
		
		// Check if we even have a cancelable query at this point
		if (!optQueryId.isPresent()) {
			task.run();
			return;
		}
		
		// Check if a timeout value has been set
		if (timeoutMillis == 0L) {
			task.run();
			return;
		}

		// Create a future that we'll use the propagate timeouts to the caller
		final CompletableFuture<SQLTimeoutException> killFuture = new CompletableFuture<>();

		// Capture the current thread that will block waiting for a response from the server
		final Thread submittingThread = Thread.currentThread();
		
		// Create a task that will cancel this query if the timeout has been exceeded
		final TimerTask killQueryTask = new TimerTask(){
			
			@Override
			public void run() {

				// execute the cancel routine iff it's still active
				final long timeoutSec = timeoutMillis / 1000;
				
				LOGGER.log(Level.INFO, String.format(
					"Timeout invoked after %s seconds. Canceling query %s", timeoutSec, optQueryId.get()));
					
					// send the kill query message on the timeout thread. This is okay because we don't
					// share Timers across connection threads.
					Exception suppressed = null;
					try {

						// interrupt the thread waiting for the server response
						submittingThread.interrupt();

						// we can't reuse the existing socket because it can now have garbage sitting
						// on it (from the timed out request). We could add sequence numbers to our 
						// protocol but that's a heavy handed solution. The easist thing to do here
						// is to tear down our current connection.
						conn.reconnect();

						// set the result set to null. We forego closing it because the server sql node
						// should clean up all resources related to this query. 
						conn.rs = null; 

						// send the kill query message to the server
						XGStatement.this.killQuery(optQueryId.get());
					} catch (Exception e) {
						LOGGER.log(Level.WARNING, "Error sending kill query message", e);
						suppressed = e;
					} finally {
						final SQLTimeoutException e = new SQLTimeoutException(String.format("Timeout of %s seconds exceeded", timeoutSec));
						if (suppressed != null) {
							e.addSuppressed(suppressed);
						}
						
						// return the timeout exception to the blocking caller
						killFuture.complete(e);
					}
				}
			};
			
		conn.addTimeout(killQueryTask, timeoutMillis);

		try {
			// run the task
			task.run();
		} finally {
			// Our task completed or we were interrupted
			if (!killQueryTask.cancel()) {
				// this is ugly, but we're within the context of a synchronous framework so whatever
				SQLException e = killFuture.join(); // wait for the kill query response (don't interrupt)
				Thread.interrupted(); // clear interrupted condition
				throw e;
			} else {
				// Removes our canceled task (any those from any other connection) from the timer task queue
				conn.purgeTimeoutTasks();
			}
		}
	}

	@Override
	public void addBatch(final String sql) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void cancel() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void clearBatch() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void clearWarnings() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		warnings.clear();
	}

	@Override
	public void close() throws SQLException {
		if (this.result != null)
		{
			result.close();
		}

		dissociateQuery();
		result = null;
		closed = true;
	}

	@Override
	public void closeOnCompletion() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(String sql) throws SQLException {
		clearWarnings();
		sql = sql.trim();
		
		while (sql.startsWith("--") || sql.startsWith("/*"))
		{
			if (sql.startsWith("--"))
			{
				//Single line comment
				int index = sql.indexOf('\n');
		
				if  (index == -1)
				{
					sql = "";
				}
				else
				{
					sql = sql.substring(index + 1).trim();
				}
			}
		
			if (sql.startsWith("/*"))
			{
				//Multi-line comment
				int index = sql.indexOf("*/");
				if (index == -1)
				{
					sql = "";
				}
				else
				{
					sql = sql.substring(index + 2).trim();
				}
			}
		}
		
		if (sql.toUpperCase().startsWith("SELECT") || sql.toUpperCase().startsWith("WITH"))
		{
			this.result = (XGResultSet) executeQuery(sql);
			return true;
		}
		else
		{
			this.executeUpdate(sql);
			return false;
		}
	}

	@Override
	public boolean execute(final String sql, final int autoGeneratedKeys) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(final String sql, final int[] columnIndexes) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public boolean execute(final String sql, final String[] columnNames) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int[] executeBatch() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	private static boolean startsWithIgnoreCase(final String in, final String cmp) {
		int firstNonParentheses = 0;
		int len = in.length();
		while (firstNonParentheses < len && in.charAt(firstNonParentheses) == '(') {
			firstNonParentheses++;
		}
		if (in.substring(firstNonParentheses).toUpperCase().startsWith(cmp.toUpperCase())) {
			return true;
		}

		return false;
	}

	@Override
	public ResultSet executeQuery(String sql) throws SQLException {
		String explain = "";
		boolean isExplain = false;
    	sql = sql.trim();
		if (startsWithIgnoreCase(sql, "EXPLAIN JSON")) {
			final String sqlQuery = sql.substring("EXPLAIN JSON" .length()).trim();
			try {
				//get the plan in proto format and convert it to its Json representation
				final PlanMessage pm = explain(sqlQuery);
				explain = JsonFormat.printer().print(pm);
			} catch (Exception e) {
				throw SQLStates.newGenericException(e);
			}
			isExplain = true;
		}
		else if (startsWithIgnoreCase(sql, "EXPLAIN")) {
			final String sqlQuery = sql.substring("EXPLAIN ".length()).trim();

			//get the plan in proto format and convert it to its google proto buffer string representation
			final PlanMessage pm = explain(sqlQuery);
			explain = pm.toString();
			isExplain = true;
		}

		if(isExplain) {
			//split the proto string using the line break delimiter and build an one string column resultset.
			ArrayList<Object> rs = new ArrayList<>();
			String lines[] = explain.split("\\r?\\n");

			for(int i = 0; i < lines.length; i++) {
				String str = lines[i];
				ArrayList<Object> row = new ArrayList<>();
				row.add(str);
				rs.add(row);
			}
			result = conn.rs = new XGResultSet(conn, rs, this);
			this.updateCount = -1;
			return result;
		}
			
    //Handle maxRows
		if (maxRows != 0)
		{
			sql =  "WITH THE_USER_QUERY_TO_ADD_A_LIMIT_TO as (" + sql + ") SELECT * FROM THE_USER_QUERY_TO_ADD_A_LIMIT_TO LIMIT " + maxRows;
		}
    
		sendAndReceive(sql, Request.RequestType.EXECUTE_QUERY, 0, false);
		try
		{
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		}
		catch (final Exception e)
		{
			LOGGER.log( Level.WARNING, "executeQuery: "+sql, e);
			try
			{
				reconnect();
			}
			catch (final Exception reconnectException)
			{
				LOGGER.log( Level.WARNING, "executeQuery: reconnect", reconnectException);
				if(reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}

			return executeQuery(sql);
		}
		this.updateCount = -1;
		return result;
	}

	@Override
	public int executeUpdate(String sql) throws SQLException {
		//if this is a set command we just use a separately crafted proto message to make things simpler
		sql = sql.trim();
		if(sql.toUpperCase().startsWith("SET PSO")) {
			String ending = sql.toUpperCase().substring("SET PSO".length());
			ending = ending.trim();
			if(ending.equals("ON") || ending.equals("OFF")) {
				try {
					conn.setPSO(ending.equals("ON"));
				} catch (final Exception e) {
					if(e instanceof SQLException) {
						throw (SQLException) e;
					}
					
					throw SQLStates.newGenericException(e);
				}
			}
			else {
				try {
					long threshold = Long.parseLong(ending);
					try {
						conn.setPSO(threshold);
					} catch (final Exception e) {
						if(e instanceof SQLException) {
							throw (SQLException) e;
						}
					
						throw SQLStates.newGenericException(e);
					}
				} catch (final NumberFormatException e) {
					throw SQLStates.SYNTAX_ERROR.cloneAndSpecify("SET PSO command requires argument \"ON\" or \"OFF\" or an integer, got: " + ending);
				}
			}
			
			return 0;
		}
	
		//otherwise we are handling a normal update command
		final ClientWireProtocol.ExecuteUpdateResponse.Builder eur =
				(ClientWireProtocol.ExecuteUpdateResponse.Builder) sendAndReceive(sql,
						Request.RequestType.EXECUTE_UPDATE, 0, false);
		return eur.getUpdateRowCount();
	}

	@Override
	public int executeUpdate(final String sql, final int autoGeneratedKeys) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int executeUpdate(final String sql, final int[] columnIndexes) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int executeUpdate(final String sql, final String[] columnNames) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	// used by CLI
	public PlanMessage explain(final String sql) throws SQLException {
		final ClientWireProtocol.ExplainResponse.Builder er =
				(ClientWireProtocol.ExplainResponse.Builder) sendAndReceive(sql, Request.RequestType.EXECUTE_EXPLAIN, 0,
						false);
		return er.getPlan();
	}
	
	//used by CLI
	public PlanMessage explainPlan(final String plan) throws SQLException {
		final ClientWireProtocol.ExplainResponse.Builder er = 
				(ClientWireProtocol.ExplainResponse.Builder) sendAndReceive(plan, Request.RequestType.EXPLAIN_PLAN, 0,
						false);
		return er.getPlan();	
	}
	
	//used by CLI
	public ResultSet executePlan(final String plan) throws SQLException {
		sendAndReceive(plan, Request.RequestType.EXECUTE_PLAN, 0, false);
		try
		{
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		}
		catch (final Exception e)
		{
			try
			{
				reconnect();
			}
			catch (final Exception reconnectException)
			{
				if(reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return executePlan(plan);
		}
		this.updateCount = -1;
		return result;
	}
	
	//used by CLI
	public ResultSet executeInlinePlan(final String plan) throws SQLException {
		sendAndReceive(plan, Request.RequestType.EXECUTE_INLINE_PLAN, 0, false);
		try
		{
			result = conn.rs = new XGResultSet(conn, fetchSize, this);
		}
		catch (final Exception e)
		{
			try
			{
				reconnect();
			}
			catch (final Exception reconnectException)
			{
				if(reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return executePlan(plan);
		}
		this.updateCount = -1;
		return result;
	}
	
	//used by CLI
	public ArrayList<String>  listPlan() throws SQLException {
		final ClientWireProtocol.ListPlanResponse.Builder er = 
				(ClientWireProtocol.ListPlanResponse.Builder) sendAndReceive("", Request.RequestType.LIST_PLAN, 0, false);
		ArrayList<String> planNames = new ArrayList<String> (er.getPlanNameCount());
		for(int i=0; i<er.getPlanNameCount(); ++i)
			planNames.add(er.getPlanName(i));

		return planNames;	
	}

	//used by CLI
	public void cancelQuery(String uuid) throws SQLException {
		final ClientWireProtocol.CancelQueryResponse.Builder er = 
				(ClientWireProtocol.CancelQueryResponse.Builder) sendAndReceive(uuid, Request.RequestType.CANCEL_QUERY, 0, false);
		return;
	}
	
	public void killQuery(String uuid) throws SQLException {
		final ClientWireProtocol.KillQueryResponse.Builder er = 
				(ClientWireProtocol.KillQueryResponse.Builder) sendAndReceive(uuid, Request.RequestType.KILL_QUERY, 0, false);
		return;
	}
	
	//used by CLI
	public ArrayList<SysQueriesRow> listAllQueries() throws SQLException {
		final ClientWireProtocol.SystemWideQueriesResponse.Builder er = 
				(ClientWireProtocol.SystemWideQueriesResponse.Builder) sendAndReceive("", Request.RequestType.SYSTEM_WIDE_QUERIES, 0, false);
			
		ArrayList<SysQueriesRow> queries = new ArrayList<SysQueriesRow> (er.getRowsCount());
		for(int i=0; i<er.getRowsCount(); ++i) {
			queries.add( er.getRows(i) );
		}

		return queries;
	}

	//used by CLI
	public String exportTable(final String table) throws SQLException {
		final ClientWireProtocol.ExecuteExportResponse.Builder er =
				(ClientWireProtocol.ExecuteExportResponse.Builder) sendAndReceive(table, Request.RequestType.EXECUTE_EXPORT, 0, false);
		return er.getExportStatement();
	}
	
	// used by Spark
	// val is the size of each partition (if isInMb is true), or the number of partitions (otherwise)
	public PlanMessage explain(final String sql, final int val, final boolean isInMb) throws SQLException {
		final ClientWireProtocol.ExplainResponse.Builder er =
				(ClientWireProtocol.ExplainResponse.Builder) sendAndReceive(sql,
						Request.RequestType.EXECUTE_EXPLAIN_FOR_SPARK, val, isInMb);
	
		return er.getPlan();
	}

	private ClientWireProtocol.FetchSystemMetadataResponse.Builder fetchSystemMetadata(
			final FetchSystemMetadata.SystemMetadataCall call, final String schema, final String table,
			final String col, final boolean test) throws SQLException {
		clearWarnings();
		if (conn.rs != null && !conn.rs.isClosed())
		{
			throw SQLStates.PREVIOUS_RESULT_SET_STILL_OPEN.clone();
		}

		try
		{
			final FetchSystemMetadata.Builder b1 = FetchSystemMetadata.newBuilder();
			b1.setCall(call);
			// these checks aren't necessary (we know what parameters will be used from the call)
			// but they mean that the has_* methods will be accurate, if we ever care to use them
			if ((schema != null) && (!schema.equals("")))
			{
				b1.setSchema(schema);
			}
			if ((call == FetchSystemMetadata.SystemMetadataCall.GET_VIEWS) && (table != null) && (!table.equals("")))
			{
				b1.setView(table); 
			}
			else if ((table != null) && (!table.equals("")))
			{
				b1.setTable(table);
			}
			if ((col != null) && (!col.equals("")))
			{
				b1.setColumn(col);
			}
			b1.setTest(test);
			final Request.Builder b2 = Request.newBuilder();
			b2.setType(Request.RequestType.FETCH_SYSTEM_METADATA);
			b2.setFetchSystemMetadata(b1.build());
			final Request wrapper = b2.build();
			final ClientWireProtocol.FetchSystemMetadataResponse.Builder br =
					ClientWireProtocol.FetchSystemMetadataResponse.newBuilder();
			try
			{
				conn.out.write(intToBytes(wrapper.getSerializedSize()));
				wrapper.writeTo(conn.out);
				conn.out.flush();

				// get confirmation
				final int length = getLength();
				final byte[] data = new byte[length];
				readBytes(data);
				br.mergeFrom(data);

				final ConfirmationResponse response = br.getResponse();
				final ResponseType rType = response.getType();
				processResponseType(rType, response);

				return br;
			}
			catch (SQLException | IOException e)
			{
				LOGGER.log( Level.WARNING, "fetchSystemMetadataResponse: ", e);
				if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e))
				{
					throw e;
				}
				reconnect(); // try this at most once--if every node is down, report failure
				return fetchSystemMetadata(call, schema, table, col, test);
			}
		}
		catch (final Exception e)
		{
			LOGGER.log( Level.WARNING, "fetchSystemMetadataResponse: final ", e);
			if (e instanceof SQLException)
			{
				throw (SQLException) e;
			}
			throw SQLStates.newGenericException(e);
		}
	}

	public int fetchSystemMetadataInt(final FetchSystemMetadata.SystemMetadataCall call) throws SQLException {
		return fetchSystemMetadata(call, "", "", "", false).getIntVal();
	}

	public ResultSet fetchSystemMetadataResultSet(final FetchSystemMetadata.SystemMetadataCall call,
			final String schema, final String table, final String col, final boolean test) throws SQLException {
		try
		{
			conn.rs = new XGResultSet(conn, fetchSize, this,
					fetchSystemMetadata(call, schema, table, col, test).getResultSetVal());
			// DatabaseMetaData won't pass on the statement, only the result set,
			// so save any warnings there
			conn.rs.addWarnings(warnings);
			result = conn.rs;
		}
		catch (final Exception e)
		{
			LOGGER.log( Level.WARNING, "fetchSystemMetadataResultSet: ", e);
			try
			{
				reconnect();
			}
			catch (final Exception reconnectException)
			{
				LOGGER.log( Level.WARNING, "fetchSystemMetadataResultSet: reconnect", reconnectException);
				if(reconnectException instanceof SQLException) {
					throw (SQLException) reconnectException;
				}
				throw SQLStates.newGenericException(reconnectException);
			}
			return fetchSystemMetadataResultSet(call, schema, table, col, test);
		}
		this.updateCount = -1;
		return result;
	}

	public String fetchSystemMetadataString(final FetchSystemMetadata.SystemMetadataCall call) throws SQLException {
		return fetchSystemMetadata(call, "", "", "", false).getStringVal();
	}

	@Override
	public Connection getConnection() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return conn;
	}

	@Override
	public int getFetchDirection() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.FETCH_FORWARD;
	}

	@Override
	public int getFetchSize() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return fetchSize;
	}

	@Override
	public ResultSet getGeneratedKeys() throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	private int getLength() throws Exception {
		int count = 4;
		final byte[] data = new byte[4];
		while (count > 0)
		{
			final int temp = conn.in.read(data, 4 - count, count);
			if (temp == -1)
			{
				throw SQLStates.UNEXPECTED_EOF.clone();
			}

			count -= temp;
		}

		return bytesToInt(data);
	}

	@Override
	public int getMaxFieldSize() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		return 0;
	}

	@Override
	public int getMaxRows() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		
		return maxRows;
	}

	@Override
	public boolean getMoreResults() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (result != null)
		{
			result.close();
			result = null;
			dissociateQuery();
		}

		return false;
	}

	@Override
	public boolean getMoreResults(final int current) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public int getQueryTimeout() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return Math.toIntExact((int) (timeoutMillis / 1000));
	}

	protected long getQueryTimeoutMillis() {
		return timeoutMillis;
	}

	@Override
	public ResultSet getResultSet() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return result;
	}

	@Override
	public int getResultSetConcurrency() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.CONCUR_READ_ONLY;
	}

	@Override
	public int getResultSetHoldability() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.CLOSE_CURSORS_AT_COMMIT;
	}

	@Override
	public int getResultSetType() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return ResultSet.TYPE_FORWARD_ONLY;
	}

	@Override
	public int getUpdateCount() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return updateCount;
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
	public boolean isCloseOnCompletion() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return false;
	}

	@Override
	public boolean isPoolable() throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		return false;
	}

	@Override
	public boolean isWrapperFor(final Class<?> iface) throws SQLException {
		return false;
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

	private void readBytes(final byte[] bytes) throws Exception {
		int count = 0;
		final int size = bytes.length;
		while (count < size)
		{
			final int temp = conn.in.read(bytes, count, bytes.length - count);
			if (temp == -1)
			{
				throw SQLStates.UNEXPECTED_EOF.clone();
			}
			else
			{
				count += temp;
			}
		}

		return;
	}

	private void reconnect() throws IOException, SQLException {
		conn.reconnect();
		return;
	}

	private void redirect(final String host, final int port) throws IOException, SQLException {
		conn.redirect(host, port);
		oneShotForce = true;
		conn.clearOneShotForce();
		return;
	}

	private Object sendAndReceive(String sql, final Request.RequestType requestType, final int val,
			final boolean isInMb) throws SQLException {
		clearWarnings();
		if (conn.rs != null && !conn.rs.isClosed())
		{
			throw SQLStates.PREVIOUS_RESULT_SET_STILL_OPEN.clone();
		}

		// Lord forgive us for our reflective ways, an abject abuse of power.
		try
		{
			Object b1, br;
			Class<?> c;
			Method setWrapped;
			final Request.Builder b2 = Request.newBuilder();
			boolean forceFlag = true;
			boolean redirectFlag = true;
			boolean hasQueryId = false; // set to true if the query ID is encoded in the response message
			switch (requestType)
			{
				case EXECUTE_QUERY:
					c = ExecuteQuery.class;
					b1 = ExecuteQuery.newBuilder();
					br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteQuery", c);
					hasQueryId = true;
					break;
				case EXECUTE_EXPLAIN:
					c = ExecuteExplain.class;
					b1 = ExecuteExplain.newBuilder();
					br = ClientWireProtocol.ExplainResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteExplain", c);
					break;
				case EXECUTE_EXPLAIN_FOR_SPARK:
					c = ExecuteExplainForSpark.class;
					b1 = ExecuteExplainForSpark.newBuilder();
					br = ClientWireProtocol.ExplainResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteExplainForSpark", c);
					break;
				case EXECUTE_UPDATE:
					c = ExecuteUpdate.class;
					b1 = ExecuteUpdate.newBuilder();
					br = ClientWireProtocol.ExecuteUpdateResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteUpdate", c);
					break;
				case EXECUTE_PLAN:
					c = ExecutePlan.class;
					b1 = ExecutePlan.newBuilder();
					br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecutePlan", c);
					break;
				case EXECUTE_INLINE_PLAN:
					c = ExecuteInlinePlan.class;
					b1 = ExecuteInlinePlan.newBuilder();
					br = ClientWireProtocol.ExecuteQueryResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteInlinePlan", c);
					break;
				case EXPLAIN_PLAN:
					c = ExplainPlan.class;
					b1 = ExplainPlan.newBuilder();
					br = ClientWireProtocol.ExplainResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExplainPlan", c);
					break;
				case LIST_PLAN:
					c = ListPlan.class;
					b1 = ListPlan.newBuilder();
					br = ClientWireProtocol.ListPlanResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setListPlan", c);
					break;
				case CANCEL_QUERY:
					c = CancelQuery.class;
					b1 = CancelQuery.newBuilder();
					br = ClientWireProtocol.CancelQueryResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setCancelQuery", c);
					forceFlag = false;
					redirectFlag = false;
					break;
				case SYSTEM_WIDE_QUERIES:
					c = SystemWideQueries.class;
					b1 = SystemWideQueries.newBuilder();
					br = ClientWireProtocol.SystemWideQueriesResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setSystemWideQueries", c);
					forceFlag = false;
					redirectFlag = false;
					break;
				case KILL_QUERY:
					c = KillQuery.class;
					b1 = KillQuery.newBuilder();
					br = ClientWireProtocol.KillQueryResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setKillQuery", c);
					forceFlag = false;
					redirectFlag = false;
					break;
				case EXECUTE_EXPORT:
					c = ExecuteExport.class;
					b1 = ExecuteExport.newBuilder();
					br = ClientWireProtocol.ExecuteExportResponse.newBuilder();
					setWrapped = b2.getClass().getMethod("setExecuteExport", c);
					forceFlag = false;
					redirectFlag = false;
					break;
				default:
					throw SQLStates.INTERNAL_ERROR.clone();
			}
			if (requestType == Request.RequestType.EXECUTE_EXPLAIN_FOR_SPARK)
			{
				final Method setType = b1.getClass().getMethod("setType", PartitioningType.class);
				if (isInMb)
				{
					setType.invoke(b1, PartitioningType.BY_SIZE);
				}
				else
				{
					setType.invoke(b1, PartitioningType.BY_NUMBER);
				}
				b1.getClass().getMethod("setPartitioningParam", int.class).invoke(b1, val);
			}
			else
			{
				sql = setParms(sql);
			}

			if (sql.length() > 0) 
			{
				b1.getClass().getMethod("setSql", String.class).invoke(b1, sql);
				if(forceFlag)
				{
					final Method setForce = b1.getClass().getMethod("setForce", boolean.class);
					setForce.invoke(b1, force);
					if (oneShotForce)
					{
						setForce.invoke(b1, true);
						oneShotForce = false;
					}
				}
			}
			
			b2.getClass().getMethod("setType", requestType.getClass()).invoke(b2, requestType);
			setWrapped.invoke(b2, c.cast(b1.getClass().getMethod("build").invoke(b1)));
			final Request wrapper = (Request) b2.getClass().getMethod("build").invoke(b2);
			try
			{
				conn.out.write(intToBytes(wrapper.getSerializedSize()));
				wrapper.writeTo(conn.out);
				conn.out.flush();
				// get confirmation
				final int length = getLength();
				final byte[] data = new byte[length];
				readBytes(data);
				br.getClass().getMethod("mergeFrom", byte[].class).invoke(br, data);
				
				final Method getResponse = br.getClass().getMethod("getResponse");
				final ConfirmationResponse response = (ConfirmationResponse) getResponse.invoke(br);
				final ResponseType rType = response.getType();
				processResponseType(rType, response);
				
				if(redirectFlag)
				{
					final Method getRedirect = br.getClass().getMethod("getRedirect");
					if ((boolean) getRedirect.invoke(br))
					{
						final Method getRedirectHost = br.getClass().getMethod("getRedirectHost");
						final Method getRedirectPort = br.getClass().getMethod("getRedirectPort");
						redirect((String) getRedirectHost.invoke(br), (int) getRedirectPort.invoke(br));
						return sendAndReceive(sql, requestType, val, isInMb);
					}
				}

				if (hasQueryId) {
					final Method getQueryId = br.getClass().getMethod("getQueryId");
					final String recvQueryId = ((String) getQueryId.invoke(br));
					if (!recvQueryId.isEmpty())
					{
						associateQuery(recvQueryId);
					}
				}

				return br;
			}
			catch (SQLException | IOException e)
			{
				if (e instanceof SQLException && !SQLStates.UNEXPECTED_EOF.equals((SQLException) e))
				{
					throw e;
				}
				reconnect(); // try this at most once--if every node is down, report failure
				return sendAndReceive(sql, requestType, val, isInMb);
			}
		}
		catch (final Exception e)
		{
			if (e instanceof SQLException)
			{
				throw (SQLException) e;
			}
			throw SQLStates.newGenericException(e);
		}
	}

	@Override
	public void setCursorName(final String name) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setEscapeProcessing(final boolean enable) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setFetchDirection(final int direction) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setFetchSize(final int rows) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}

		if (rows < 0)
		{
			throw SQLStates.INVALID_ARGUMENT.clone();
		}

		if(rows == 0) {
			//switch back to the default settings
			fetchSize = defaultFetchSize;
		}
		else {
			fetchSize = rows;
		}
	}

	@Override
	public void setMaxFieldSize(final int max) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setMaxRows(final int max) throws SQLException {
		if (closed)
		{
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		
		maxRows = max;
	}

	private String setParms(final String in) throws SQLException {
		String out = "";
		int x = 0;
		int i = 0;
		boolean quoted = false;
		int quoteType = 0;
		final int size = in.length();
		while (i < size)
		{
			if ((in.charAt(i) != '\'' && in.charAt(i) != '"') || (in.charAt(i) == '\'' && quoteType == 2)
					|| (in.charAt(i) == '"' && quoteType == 1))
			{
				if (!quoted)
				{
					if (in.charAt(i) == '?')
					{
						try
						{
							final Object parm = parms.get(x);
							
							//System.out.println("parm type: " + parm.getClass());
							
							if (parm == null)
							{
								out += "NULL";
							}
							else if (parm instanceof String)
							{
								out += ("'" + ((String) parm).replace("'", "''") + "'");
							}
							else if (parm instanceof Timestamp)
							{
								final SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd HH:mm:ss.SSS");
								final TimeZone utc = TimeZone.getTimeZone("UTC");
								format.setTimeZone(utc);
								out += ("TIMESTAMP('" + format.format((Timestamp) parm) + "')");
							}
							else if (parm instanceof Boolean)
							{
								//System.out.println("inside BOOLEAN set param");
								out += ("BOOLEAN('" + parm + "')");
							}
							else if (parm instanceof byte[])
							{
								out += ("BINARY('0x" + bytesToHex((byte[]) parm) + "')");
							}
							else if (parm instanceof Date)
							{
								final SimpleDateFormat format = new SimpleDateFormat("yyyy-MM-dd");
								final TimeZone utc = TimeZone.getTimeZone("UTC");
								format.setTimeZone(utc);
								out += ("DATE('" + format.format((Date) parm) + "')");
							}
                            else if (parm instanceof Time)
                            {
                                final SimpleDateFormat format = new SimpleDateFormat("HH:mm:ss.SSS");
                                final TimeZone utc = TimeZone.getTimeZone("UTC");
                                format.setTimeZone(utc);
                                out += ("TIME('" + format.format((Time) parm) + "')");
                            }
							else
							{
								//System.out.println("inside set param default else case");
								out += parm;
							}
						}
						catch (final IndexOutOfBoundsException e)
						{
							throw SQLStates.INVALID_PARAMETER_MARKER.clone();
						}

						x++;
					}
					else
					{
						out += in.charAt(i);
					}
				}
				else
				{
					out += in.charAt(i);
				}
			}
			else
			{
				if (quoteType == 0)
				{
					if (in.charAt(i) == '\'' && ((i + 1) == in.length() || in.charAt(i + 1) != '\''))
					{
						quoteType = 1;
						quoted = true;
						out += '\'';
					}
					else if (in.charAt(i) == '"' && ((i + 1) == in.length() || in.charAt(i + 1) != '"'))
					{
						quoteType = 2;
						quoted = true;
						out += '"';
					}
					else
					{
						out += in.charAt(i);
						out += in.charAt(i + 1);
						i++;
					}
				}
				else if (quoteType == 1)
				{
					if (in.charAt(i) == '\'' && ((i + 1) == in.length() || in.charAt(i + 1) != '\''))
					{
						quoteType = 0;
						quoted = false;
						out += '\'';
					}
					else if (in.charAt(i) == '"')
					{
						out += '"';
					}
					else
					{
						out += "''";
						i++;
					}
				}
				else
				{
					if (in.charAt(i) == '"' && ((i + 1) == in.length() || in.charAt(i + 1) != '"'))
					{
						quoteType = 0;
						quoted = false;
						out += '"';
					}
					else if (in.charAt(i) == '\'')
					{
						out += '\'';
					}
					else
					{
						out += "\"\"";
						i++;
					}
				}
			}

			i++;
		}

		return out;
	}

	@Override
	public void setPoolable(final boolean poolable) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}

	@Override
	public void setQueryTimeout(final int seconds) throws SQLException {
		if (closed) {
			throw SQLStates.CALL_ON_CLOSED_OBJECT.clone();
		}
		if (seconds < 0) {
			throw new SQLWarning(String.format("timeout value must be non-negative, was: %s", seconds));
		}
		timeoutMillis = seconds * 1000;
		LOGGER.log(Level.FINE, "Query timeout set to {} seconds", seconds);
	}
	
	@Override
	public <T> T unwrap(final Class<T> iface) throws SQLException {
		throw new SQLFeatureNotSupportedException();
	}
}

