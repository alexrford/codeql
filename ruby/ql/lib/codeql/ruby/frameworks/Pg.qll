/**
 * Provides modeling for Pg, a Ruby library (gem) for interacting with PostgreSQL databases.
 */

private import codeql.ruby.ApiGraphs
private import codeql.ruby.dataflow.FlowSummary
private import codeql.ruby.Concepts

/**
 * Provides modeling for Pg, a Ruby library (gem) for interacting with PostgreSQL databases.
 */
module Pg {
  /**
   * Flow summary for `PG.new()`. This method wraps a SQL string, marking it as
   * safe.
   */
  private class SqlSummary extends SummarizedCallable {
    SqlSummary() { this = "PG.new()" }

    override MethodCall getACall() { result = any(PgConnection c).asExpr().getExpr() }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      input = "Argument[0]" and output = "ReturnValue" and preservesValue = false
    }
  }

  /** A call to PG::Connection.open() is used to establish a connection to a PostgreSQL database. */
  private class PgConnection extends DataFlow::CallNode {
    PgConnection() {
      this =
        API::getTopLevelMember("PG")
            .getMember("Connection")
            .getAMethodCall(["open", "new", "connect_start"])
      or
      this = API::getTopLevelMember("PG").getAnInstantiation()
    }
  }

  /** A call that executes SQL statements against a PostgreSQL database. */
  private class PgConstruction extends SqlExecution::Range, DataFlow::CallNode {
    private DataFlow::Node query;

    PgConstruction() {
      exists(PgConnection pgConnection |
        this =
          pgConnection.getAMethodCall(["exec", "async_exec", "exec_params", "async_exec_params"]) and
        query = this.getArgument(0)
        or
        exists(string queryName, DataFlow::CallNode prepareCall |
          this = pgConnection.getAMethodCall("exec_prepared") and
          prepareCall = pgConnection.getAMethodCall("prepare") and
          prepareCall.getArgument(0).getConstantValue().isStringlikeValue(queryName) and
          this.getArgument(0).getConstantValue().isStringlikeValue(queryName) and
          query = prepareCall.getArgument(1)
        )
      )
    }

    override DataFlow::Node getSql() { result = query }
  }
}
