/**
 * Provides classes and predicates used by the XSS queries.
 */

private import codeql.ruby.AST
private import codeql.ruby.DataFlow
private import codeql.ruby.CFG
private import codeql.ruby.Concepts
private import codeql.ruby.Frameworks
private import codeql.ruby.frameworks.ActionController
private import codeql.ruby.frameworks.ActionView
private import codeql.ruby.frameworks.Rails
private import codeql.ruby.dataflow.RemoteFlowSources
private import codeql.ruby.dataflow.BarrierGuards
private import codeql.ruby.dataflow.internal.DataFlowDispatch

/**
 * Provides default sources, sinks and sanitizers for detecting
 * "server-side cross-site scripting" vulnerabilities, as well as
 * extension points for adding your own.
 */
private module Shared {
  newtype FlowState =
    UnmarkedAndTainted() or
    MarkedSafeAndUntainted() or
    MarkedSafeAndTainted()

  /**
   * A data flow source for "server-side cross-site scripting" vulnerabilities.
   */
  abstract class Source extends DataFlow::Node { }

  /**
   * A data flow sink for "server-side cross-site scripting" vulnerabilities.
   */
  abstract class Sink extends DataFlow::Node {
    abstract FlowState getState();
  }

  /**
   * A sanitizer for "server-side cross-site scripting" vulnerabilities.
   */
  abstract class Sanitizer extends DataFlow::Node { }

  private class ErbOutputMethodCallArgumentNode extends DataFlow::Node {
    private MethodCall call;

    ErbOutputMethodCallArgumentNode() {
      exists(ErbOutputDirective d |
        call = d.getTerminalStmt() and
        this.asExpr().getExpr() = call.getAnArgument()
      )
    }

    MethodCall getCall() { result = call }
  }

  /**
   * A value interpolated using a raw erb output directive, which does not perform HTML escaping.
   * ```erb
   * <%== sink %>
   * ```
   */
  class ErbRawOutputDirective extends Sink {
    ErbRawOutputDirective() {
      exists(ErbOutputDirective d | d.isRaw() | this.asExpr().getExpr() = d.getTerminalStmt())
    }

    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  class ErbSafeOutputDirective extends Sink {
    ErbSafeOutputDirective() {
      exists(ErbOutputDirective d | not d.isRaw() | this.asExpr().getExpr() = d.getTerminalStmt())
    }

    override FlowState getState() { result = MarkedSafeAndTainted() }
  }

  /**
   * An argument to a call to the `raw` method, considered as a flow sink.
   */
  class RawCallArgumentAsSink extends Sink, ErbOutputMethodCallArgumentNode {
    RawCallArgumentAsSink() { this.getCall() instanceof RawCall }

    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  /**
   * An argument to an ActionView helper method which is not escaped,
   * considered as a flow sink.
   */
  class RawHelperCallArgumentAsSink extends Sink {
    RawHelperCallArgumentAsSink() {
      exists(ErbOutputDirective d, ActionView::Helpers::RawHelperCall c |
        d.getTerminalStmt() = c and this.asExpr().getExpr() = c.getRawArgument()
      )
    }

    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  /**
   * An argument that is used to construct the `src` attribute of a `<script>`
   * tag.
   */
  class ArgumentInterpretedAsUrlAsSink extends Sink, ErbOutputMethodCallArgumentNode,
    ActionView::ArgumentInterpretedAsUrl
  {
    // TODO: verify
    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  /**
   * A argument to a call to the `link_to` method, which does not expect
   * unsanitized user-input, considered as a flow sink.
   */
  class LinkToCallArgumentAsSink extends Sink, ErbOutputMethodCallArgumentNode {
    LinkToCallArgumentAsSink() {
      this.asExpr().getExpr() = this.getCall().(LinkToCall).getPathArgument()
    }

    // TODO: verify
    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  /** A write to an HTTP response header, considered as a flow sink. */
  class HeaderWriteAsSink extends Sink {
    HeaderWriteAsSink() {
      exists(Http::Server::HeaderWriteAccess a |
        a.getName() = ["content-type", "access-control-allow-origin"]
      |
        this = a.getValue()
      )
    }

    // TODO: verify
    override FlowState getState() {
      result = UnmarkedAndTainted()
      or
      result = MarkedSafeAndTainted()
    }
  }

  /**
   * An HTML escaping, considered as a sanitizer.
   */
  class HtmlEscapingAsSanitizer extends Sanitizer {
    HtmlEscapingAsSanitizer() { this = any(HtmlEscaping esc).getOutput() }
  }

  /**
   * A comparison with a constant string, considered as a sanitizer-guard.
   */
  class StringConstCompareAsSanitizer extends Sanitizer, StringConstCompareBarrier { }

  /**
   * An inclusion check against an array of constant strings, considered as a sanitizer-guard.
   */
  class StringConstArrayInclusionCallAsSanitizer extends Sanitizer,
    StringConstArrayInclusionCallBarrier
  { }

  /**
   * A `VariableWriteAccessCfgNode` that is not succeeded (locally) by another
   * write to that variable.
   */
  private class FinalInstanceVarWrite extends CfgNodes::ExprNodes::InstanceVariableWriteAccessCfgNode
  {
    private InstanceVariable var;

    FinalInstanceVarWrite() {
      var = this.getExpr().getVariable() and
      not exists(CfgNodes::ExprNodes::InstanceVariableWriteAccessCfgNode succWrite |
        succWrite.getExpr().getVariable() = var
      |
        succWrite = this.getASuccessor+()
      )
    }

    InstanceVariable getVariable() { result = var }

    AssignExpr getAnAssignExpr() { result.getLeftOperand() = this.getExpr() }
  }

  /**
   * Holds if `call` is a method call in ERB file `erb`, targeting a method
   * named `name`.
   */
  pragma[noinline]
  private predicate isMethodCall(MethodCall call, string name, ErbFile erb) {
    name = call.getMethodName() and
    erb = call.getLocation().getFile()
  }

  /**
   * Holds if `action` contains an assignment of `value` to an instance
   * variable named `name`, in ERB file `erb`.
   */
  pragma[noinline]
  private predicate actionAssigns(
    ActionControllerActionMethod action, string name, Expr value, ErbFile erb
  ) {
    exists(AssignExpr ae, FinalInstanceVarWrite controllerVarWrite |
      action.getDefaultTemplateFile() = erb and
      ae.getParent+() = action and
      ae = controllerVarWrite.getAnAssignExpr() and
      name = controllerVarWrite.getVariable().getName() and
      value = ae.getRightOperand()
    )
  }

  pragma[noinline]
  private predicate isVariableReadAccess(VariableReadAccess viewVarRead, string name, ErbFile erb) {
    erb = viewVarRead.getLocation().getFile() and
    viewVarRead.getVariable().getName() = name
  }

  private predicate isFlowFromControllerInstanceVariable(DataFlow::Node node1, DataFlow::Node node2) {
    // instance variables in the controller
    exists(string name, ErbFile template |
      // match read to write on variable name
      actionAssigns(_, name, node1.asExpr().getExpr(), template) and
      // propagate taint from assignment RHS expr to variable read access in view
      isVariableReadAccess(node2.asExpr().getExpr(), name, template)
    )
  }

  /**
   * Holds if `helperMethod` is a helper method named `name` that is associated
   * with ERB file `erb`.
   */
  pragma[noinline]
  private predicate isHelperMethod(
    ActionControllerHelperMethod helperMethod, string name, ErbFile erb
  ) {
    helperMethod.getName() = name and
    helperMethod.getControllerClass() = getAssociatedControllerClass(erb)
  }

  private predicate isFlowIntoHelperMethod(DataFlow::Node node1, DataFlow::Node node2) {
    // flow from template into controller helper method
    exists(
      ErbFile template, ActionControllerHelperMethod helperMethod, string name,
      CfgNodes::ExprNodes::MethodCallCfgNode helperMethodCall, int argIdx
    |
      isHelperMethod(helperMethod, name, template) and
      isMethodCall(helperMethodCall.getExpr(), name, template) and
      helperMethodCall.getArgument(pragma[only_bind_into](argIdx)) = node1.asExpr() and
      helperMethod.getParameter(pragma[only_bind_into](argIdx)) = node2.asParameter()
    )
  }

  private predicate isFlowFromHelperMethod(DataFlow::Node node1, DataFlow::Node node2) {
    // flow out of controller helper method into template
    exists(ErbFile template, ActionControllerHelperMethod helperMethod, string name |
      // `node1` is an expr node that may be returned by the helper method
      exprNodeReturnedFrom(node1, helperMethod) and
      // `node2` is a call to the helper method
      isHelperMethod(helperMethod, name, template) and
      isMethodCall(node2.asExpr().getExpr(), name, template)
    )
  }

  /**
   * An additional step that is preserves dataflow in the context of XSS.
   */
  predicate isAdditionalXssFlowStep(
    DataFlow::Node nodeFrom, FlowState stateFrom, DataFlow::Node nodeTo, FlowState stateTo
  ) {
    stateFrom = stateTo and
    (
      isFlowFromControllerInstanceVariable(nodeFrom, nodeTo)
      or
      isFlowIntoHelperMethod(nodeFrom, nodeTo)
      or
      isFlowFromHelperMethod(nodeFrom, nodeTo)
    )
    or
    exists(DataFlow::CallNode htmlSafeCall |
      htmlSafeCall.getMethodName() = "html_safe" and
      nodeTo = htmlSafeCall and
      nodeFrom = htmlSafeCall.getReceiver()
    |
      stateFrom = UnmarkedAndTainted() and stateTo = MarkedSafeAndTainted()
      or
      not stateFrom = UnmarkedAndTainted() and stateTo = stateFrom
    )
  }

  private predicate htmlSafeGuard(CfgNodes::AstCfgNode guard, CfgNode testedNode, boolean branch) {
    exists(DataFlow::CallNode html_safe_call | html_safe_call.getMethodName() = "html_safe?" |
      guard = html_safe_call.asExpr() and
      testedNode = html_safe_call.getReceiver().asExpr() and
      branch = true
    )
  }

  /** A guard that calls `.html_safe?` to check whether the string is already HTML-safe. */
  private class HtmlSafeGuard extends Sanitizer {
    HtmlSafeGuard() { this = DataFlow::BarrierGuard<htmlSafeGuard/3>::getABarrierNode() }
  }
}

/**
 * Provides default sources, sinks and sanitizers for detecting
 * "reflected cross-site scripting" vulnerabilities, as well as
 * extension points for adding your own.
 */
module ReflectedXss {
  class FlowState = Shared::FlowState;

  /** A data flow source for stored XSS vulnerabilities. */
  abstract class Source extends Shared::Source {
    abstract FlowState getState();
  }

  /** A data flow sink for stored XSS vulnerabilities. */
  class Sink = Shared::Sink;

  /** A sanitizer for stored XSS vulnerabilities. */
  class Sanitizer = Shared::Sanitizer;

  /**
   * An additional step that is preserves dataflow in the context of reflected XSS.
   */
  predicate isAdditionalXssTaintStep = Shared::isAdditionalXssFlowStep/4;

  /**
   * A HTTP request input, considered as a flow source.
   */
  class HttpRequestInputAccessAsSource extends Source, Http::Server::RequestInputAccess {
    HttpRequestInputAccessAsSource() { this.isThirdPartyControllable() }

    override FlowState getState() { result = Shared::UnmarkedAndTainted() }
  }

  /**
   * An `html_safe` call, considered as a flow source.
   */
  class HtmlSafeCallAsSource extends Source, DataFlow::CallNode {
    HtmlSafeCallAsSource() { this.getMethodName() = "html_safe" }

    override FlowState getState() { result = Shared::MarkedSafeAndUntainted() }
  }
}

private module OrmTracking {
  /**
   * A data flow configuration to track flow from finder calls to field accesses.
   */
  private module Config implements DataFlow::ConfigSig {
    predicate isSource(DataFlow::Node source) {
      // We currently only use ORM instances that come from a call site, so restrict the sources
      // to calls. This works around a performance issue that would arise from using 'self' as a source
      // in ActiveRecord models. Over time, library models should stop relying on OrmInstantiation and instead
      // use API graphs or type-tracking the same way we track other types.
      source instanceof OrmInstantiation and source instanceof DataFlow::CallNode
    }

    // Select any call receiver and narrow down later
    predicate isSink(DataFlow::Node sink) { sink = any(DataFlow::CallNode c).getReceiver() }

    // TODO: flow states?
    predicate isAdditionalFlowStep(DataFlow::Node node1, DataFlow::Node node2) {
      Shared::isAdditionalXssFlowStep(node1, _, node2, _)
    }

    predicate isBarrierIn(DataFlow::Node node) { node instanceof DataFlow::SelfParameterNode }

    int accessPathLimit() { result = 1 }
  }

  import DataFlow::Global<Config>
}

/** Provides default sources, sinks and sanitizers for detecting stored cross-site scripting (XSS) vulnerabilities. */
module StoredXss {
  class FlowState = Shared::FlowState;

  /** A data flow source for stored XSS vulnerabilities. */
  abstract class Source extends Shared::Source { }

  /** A data flow sink for stored XSS vulnerabilities. */
  class Sink = Shared::Sink;

  /** A sanitizer for stored XSS vulnerabilities. */
  class Sanitizer = Shared::Sanitizer;

  /**
   * An additional step that preserves dataflow in the context of stored XSS.
   */
  predicate isAdditionalXssTaintStep = Shared::isAdditionalXssFlowStep/4;

  private class OrmFieldAsSource extends Source instanceof DataFlow::CallNode {
    OrmFieldAsSource() {
      exists(DataFlow::CallNode subSrc |
        OrmTracking::flow(subSrc, this.getReceiver()) and
        subSrc.(OrmInstantiation).methodCallMayAccessField(this.getMethodName()) and
        this.getNumberOfArguments() = 0 and
        not exists(this.getBlock())
      )
    }
  }

  /** A file read, considered as a flow source for stored XSS. */
  private class FileSystemReadAccessAsSource extends Source instanceof FileSystemReadAccess { }
  // TODO: Consider `FileNameSource` flowing to script tag `src` attributes and similar
}
