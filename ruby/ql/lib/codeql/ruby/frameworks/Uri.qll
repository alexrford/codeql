/**
 * Provides modeling for the `URI` library.
 * https://ruby.github.io/uri/
 */

// private import codeql.ruby.AST
private import codeql.ruby.Concepts
private import codeql.ruby.DataFlow
private import codeql.ruby.FlowSummary

/**
 * Provides modeling for the `Uri` library.
 * https://ruby.github.io/uri/
 */
private module Uri {
  private class UriCall extends DataFlow::CallNode {
    UriCall() { this.getMethodName() = "URI" }

    DataFlow::Node getUri() { result = this.getArgument(0) }
  }

  private class UriSummary extends SummarizedCallable {
    UriSummary() { this = "URI()" }

    override MethodCall getACall() { result = any(UriCall c).asExpr().getExpr() }

    override predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
      input = "Argument[0]" and output = "ReturnValue" and preservesValue = false
    }
  }

  private class UriParameterCall extends DataFlow::CallNode, Http::Server::RequestInputAccess::Range
  {
    UriParameterCall() {
      this.getMethodName() = ["params", "fragment"] and
      any(UriCall c).(DataFlow::LocalSourceNode).flowsTo(this.getReceiver())
    }

    string getSourceType() { result = "URI#" + this.getMethodName() }

    Http::Server::RequestInputKind getKind() { result = Http::Server::parameterInputKind() }
  }
}
