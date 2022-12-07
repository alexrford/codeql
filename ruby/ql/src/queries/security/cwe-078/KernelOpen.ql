/**
 * @name Use of `Kernel.open`, `IO.read` or similar sinks with user-controlled input
 * @description Using `Kernel.open`, `IO.read`, `IO.write`, `IO.binread`, `IO.binwrite`,
 *              `IO.foreach`, `IO.readlines`, or `URI.open` may allow a malicious
 *              user to execute arbitrary system commands.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.8
 * @precision high
 * @id rb/kernel-open
 * @tags correctness
 *       security
 *       external/cwe/cwe-078
 *       external/cwe/cwe-088
 *       external/cwe/cwe-073
 */

import codeql.ruby.DataFlow
import codeql.ruby.TaintTracking
import codeql.ruby.dataflow.RemoteFlowSources
import DataFlow::PathGraph
import codeql.ruby.security.KernelOpenQuery
private import codeql.ruby.ApiGraphs

class Configuration extends TaintTracking::Configuration {
  Configuration() { this = "KernelOpen" }

  override predicate isSource(DataFlow::Node source, DataFlow::FlowState state) {
    source instanceof RemoteFlowSource and
    state instanceof NotFilePathSanitized
  }

  override predicate isSink(DataFlow::Node sink, DataFlow::FlowState state) {
    sink = any(AmbiguousPathCall r).getPathArgument() and
    state instanceof NotFilePathSanitized
  }

  override predicate isAdditionalTaintStep(
    DataFlow::Node nodeFrom, DataFlow::FlowState stateFrom, DataFlow::Node nodeTo,
    DataFlow::FlowState stateTo
  ) {
    nodeTo = API::getTopLevelMember("File").getAMethodCall("join") and
    stateTo instanceof FilePathSanitized and
    nodeFrom = nodeTo.(DataFlow::CallNode).getArgument(any(int i | i > 0)) and
    stateFrom instanceof NotFilePathSanitized
  }

  override predicate isAdditionalTaintStep(DataFlow::Node nodeFrom, DataFlow::Node nodeTo) {
    nodeTo = API::getTopLevelMember("File").getAMethodCall("join") and
    nodeFrom = nodeTo.(DataFlow::CallNode).getArgument(0)
  }

  override predicate isSanitizer(DataFlow::Node node) { node instanceof Sanitizer }
}

class FilePathSanitized extends DataFlow::FlowState {
  FilePathSanitized() { this = "FilePathSanitized" }
}

class NotFilePathSanitized extends DataFlow::FlowState {
  NotFilePathSanitized() { this = "NotFilePathSanitized" }
}

from
  Configuration config, DataFlow::PathNode source, DataFlow::PathNode sink,
  DataFlow::Node sourceNode, DataFlow::CallNode call
where
  config.hasFlowPath(source, sink) and
  sourceNode = source.getNode() and
  call.getArgument(0) = sink.getNode()
select sink.getNode(), source, sink,
  "This call to " + call.(AmbiguousPathCall).getName() +
    " depends on a $@. Consider replacing it with " + call.(AmbiguousPathCall).getReplacement() +
    ".", source.getNode(), "user-provided value"
