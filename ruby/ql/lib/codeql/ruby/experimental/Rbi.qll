private import codeql.ruby.AST
private import codeql.ruby.CFG
private import codeql.ruby.controlflow.CfgNodes
private import codeql.ruby.DataFlow

module Rbi {
  class RbiFile extends File {
    RbiFile() { this.getExtension() = "rbi" }
  }

  private predicate successorNodeRanked(CfgNode p, CfgNode n, int r) {
    r = 0 and n = p.getASuccessor() or
    // set an arbitrary limit on how long the successor chain can be
    r = [1..5] and exists(CfgNode p2 |
      successorNodeRanked(p, p2, r - 1) and
      not exists(SigCall s | s.asExpr() = p2) |
      n = p2.getASuccessor()
    )
  }

  abstract class RbiType extends DataFlow::Node { }

  private newtype TReturnType =
    TRbiType(RbiType t) {
      exists(ReturnsCall r | r.getReturnType() = t)
    } or
    TVoidType()

  class ReturnType extends TReturnType {
    /** Gets a textual representation of this node. */
    cached
    string toString() {
      if exists(this.getRbiType())
      then result = this.getRbiType().toString()
      else result = "(void)"
    }

    RbiType getRbiType() {
      exists(RbiType t | this = TRbiType(t) | result = t)
    }

    predicate isVoidType() {
      this = TVoidType()
    }
  }

  class SigCall extends DataFlow::CallNode {
    SigCall() { this.getMethodName() = "sig" }

    ReturnsCall getAReturnsCall() {
      result.getSigCall() = this
    }

    ParamsCall getAParamsCall() {
      result.getSigCall() = this
    }

    VoidCall getAVoidCall() {
      result.getSigCall() = this
    }

    // TODO: Support `attr_reader`/`attr_accessor`
    /**
     * Gets the method for which this call defines the type signature.
     */
    ExprNodes::MethodBaseCfgNode getAssociatedMethod() {
      result = min(ExprNodes::MethodBaseCfgNode m, int i |
        successorNodeRanked(this.asExpr(), m, i) |
        m order by i
      )
    }

    ReturnType getReturnType() {
      result.getRbiType() = this.getAReturnsCall().getReturnType() or
      (exists(this.getAVoidCall()) and result.isVoidType())
    }

    ParameterType getAParameterType() {
      result = this.getAParamsCall().getAParameterType()
    }
  }

  // TODO: top level vs. nested calls
  class SignatureDefiningCall extends DataFlow::CallNode {
    private SigCall sigCall;

    SignatureDefiningCall() {
      // TODO: can we avoid dropping to the AST level?
      exists(MethodCall c |
        c = sigCall.getBlock().asExpr().getExpr().getAChild() |
        // The typical pattern for the contents of a `sig` block is something
        // like `params(<param defs>).returns(<return type>)` - we want to
        // pick up both of these calls
        this.asExpr().getExpr() = c.getReceiver*()
      )
    }

    SigCall getSigCall() { result = sigCall }
  }

  /**
   * A call to `params`. This defines the types of parameters to a method.
   */
  class ParamsCall extends SignatureDefiningCall {
    ParamsCall() { this.getMethodName() = "params" }

    ParameterType getAParameterType() { result = this.getArgument(_).asExpr() }
  }

  /**
   * A call to `returns`. Defines the return type of a method.
   */
  class ReturnsCall extends SignatureDefiningCall {
    ReturnsCall() { this.getMethodName() = "returns" }

    RbiType getReturnType() {
      result = this.getArgument(0)
    }
  }

  // TODO: unify w/ returns call?
  /**
   * A call to `void`. Essentially a "don't-care" for the return type of a method.
   */
  class VoidCall extends SignatureDefiningCall {
    VoidCall() { this.getMethodName() = "void" }
  }

  class TReadAccess extends DataFlow::Node {
    TReadAccess() { this.asExpr().(ExprNodes::ConstantReadAccessCfgNode).getExpr().hasName("T") }
  }

  class ConstantReadAccessAsRbiType extends RbiType {
    private ExprNodes::ConstantReadAccessCfgNode acc;

    ConstantReadAccessAsRbiType() {
      acc = this.asExpr()
      // TODO: should this class be more restrictive?
    }
  }

  abstract class RbiCallType extends RbiType, DataFlow::CallNode {
    RbiCallType() { this.getReceiver() instanceof TReadAccess }
  }

  class RbiUnionType extends RbiCallType {
    RbiUnionType() { this.getMethodName() = "any" }

    RbiType getAType() { result = this.getArgument(_) }
  }

  class RbiUntypedType extends RbiCallType {
    RbiUntypedType() { this.getMethodName() = "untyped" }
  }

  class RbiNilableType extends RbiCallType {
    RbiNilableType() { this.getMethodName() = "nilable" }
  }

  class ParameterType extends ExprNodes::PairCfgNode {
    private RbiType t;

    ParameterType() { t.asExpr() = this.getValue() }

    RbiType getType() { result = t }
  }

  predicate parameterHasType(NamedParameter p, RbiType t) {
    exists(SigCall sc, ParameterType tp |
      sc.getAssociatedMethod().getExpr().getAParameter() = p and
      tp = sc.getAParamsCall().getAParameterType() and
      t = tp.getType() and
      p.getName() = tp.getKey().getConstantValue().getStringlikeValue()
    )
  }

}
