/**
 * Provides a taint-tracking configuration for detecting "reflected server-side cross-site scripting" vulnerabilities.
 *
 * Note, for performance reasons: only import this file if
 * `ReflectedXssFlow` is needed, otherwise
 * `XSS::ReflectedXss` should be imported instead.
 */

private import codeql.ruby.AST
import codeql.ruby.DataFlow
import codeql.ruby.TaintTracking

/**
 * Provides a taint-tracking configuration for detecting "reflected server-side cross-site scripting" vulnerabilities.
 * DEPRECATED: Use `ReflectedXssFlow`
 */
deprecated module ReflectedXss {
  import XSS::ReflectedXss

  /**
   * A taint-tracking configuration for detecting "reflected server-side cross-site scripting" vulnerabilities.
   * DEPRECATED: Use `ReflectedXssFlow`
   */
  deprecated class Configuration extends TaintTracking::Configuration {
    Configuration() { this = "ReflectedXSS" }

    override predicate isSource(DataFlow::Node source) { source instanceof Source }

    override predicate isSink(DataFlow::Node sink) { sink instanceof Sink }

    override predicate isSanitizer(DataFlow::Node node) { node instanceof Sanitizer }

    override predicate isAdditionalTaintStep(DataFlow::Node node1, DataFlow::Node node2) {
      isAdditionalXssTaintStep(node1, _, node2, _)
    }
  }
}

private module ReflectedXssConfig implements DataFlow::StateConfigSig {
  private import XSS::ReflectedXss as RX

  class FlowState = RX::FlowState;

  predicate isSource(DataFlow::Node source, FlowState state) {
    source.(RX::Source).getState() = state
  }

  predicate isSink(DataFlow::Node sink, FlowState state) { sink.(RX::Sink).getState() = state }

  predicate isBarrier(DataFlow::Node node) { node instanceof RX::Sanitizer }

  predicate isAdditionalFlowStep(
    DataFlow::Node node1, FlowState state1, DataFlow::Node node2, FlowState state2
  ) {
    RX::isAdditionalXssTaintStep(node1, state1, node2, state2)
  }
}

/**
 * Taint-tracking for detecting "reflected server-side cross-site scripting" vulnerabilities.
 */
module ReflectedXssFlow = TaintTracking::GlobalWithState<ReflectedXssConfig>;
