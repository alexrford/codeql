/**
 * Provides a taint-tracking configuration for reasoning about stored
 * cross-site scripting vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `StoredXssFlow` is needed, otherwise
 * `XSS::StoredXss` should be imported instead.
 */

import codeql.ruby.AST
import codeql.ruby.DataFlow
import codeql.ruby.TaintTracking

/**
 * Provides a taint-tracking configuration for cross-site scripting vulnerabilities.
 * DEPRECATED: Use StoredXssFlow
 */
deprecated module StoredXss {
  import XSS::StoredXss

  /**
   * DEPRECATED.
   *
   * A taint-tracking configuration for reasoning about Stored XSS.
   */
  deprecated class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "StoredXss" }

    override predicate isSource(DataFlow::Node source) { source instanceof Source }

    override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

    override predicate isSanitizer(DataFlow::Node node) {
      super.isSanitizer(node) or
      node instanceof Sanitizer
    }

    override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
      isAdditionalXssTaintStep(node1, _, node2, _)
    }
  }

  import TaintTracking::GlobalWithState<StoredXssConfig>
}

private module StoredXssConfig implements DataFlow::StateConfigSig {
  private import XSS::StoredXss as SX

  class FlowState = SX::FlowState;

  predicate isSource(DataFlow::Node source, FlowState state) {
    source.(SX::Source).getState() = state
  }

  predicate isSink(DataFlow::Node sink, FlowState state) { sink.(SX::Sink).getState() = state }

  predicate isBarrier(DataFlow::Node node, FlowState state) {
    node instanceof SX::Sanitizer and state.isTainted()
  }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, FlowState state1, DataFlow::Node node2, FlowState state2
  ) {
    SX::isAdditionalXssTaintStep(node1, state1, node2, state2)
  }
}

/**
 * Taint-tracking for reasoning about Stored XSS.
 */
module StoredXssFlow = TaintTracking::GlobalWithState<StoredXssConfig>;
