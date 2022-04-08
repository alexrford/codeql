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

  /** A return type of a method. */
  class ReturnType extends TReturnType {
    /** Gets a textual representation of this node. */
    cached
    string toString() {
      result = this.getRbiType().toString() or
      this.isVoidType() and result = "(void)"
    }

    /** Gets the underlying RbiType, if any. */
    RbiType getRbiType() {
      exists(RbiType t | this = TRbiType(t) | result = t)
    }

    /** Holds if this is the void type. */
    predicate isVoidType() {
      this = TVoidType()
    }
  }

  /** A call to `sig` to define the type signature of a method. */
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

  /** A call node that represents an `RbiType`. */
  abstract class RbiTypeCall extends RbiType, DataFlow::CallNode {
    RbiTypeCall() { this.getReceiver() instanceof TReadAccess }
  }

  /**
   * A call to `T.any`, - a method that takes `RbiType` parameters, and returns
   * a type representing the union of those types.
   */
  class RbiUnionType extends RbiTypeCall {
    RbiUnionType() { this.getMethodName() = "any" }

    RbiType getAType() { result = this.getArgument(_) }
  }

  /**
   * A call to `T.untyped`.
   */
  class RbiUntypedType extends RbiTypeCall {
    RbiUntypedType() { this.getMethodName() = "untyped" }
  }

  /**
   * A call to `T.nilable`, creating a nilable version of the type provided as
   * an argument.
   */
  class RbiNilableType extends RbiTypeCall {
    RbiNilableType() { this.getMethodName() = "nilable" }

    RbiType getUnderlyingType() {
      result = this.getArgument(0)
    }
  }

  /**
   * A call to `T.type_alias`. The return value of this call can be assigned to
   * create a type alias.
   */
  class RbiTypeAlias extends RbiTypeCall {
    RbiTypeAlias() { this.getMethodName() = "type_alias" }

    // TODO: avoid mapping to AST layer
    /**
     * Gets the type aliased by this call.
     */
    RbiType getAliasedType() {
      result.asExpr().getExpr() = this.getBlock().asExpr().(ExprNodes::StmtSequenceCfgNode).getExpr().getLastStmt()
    }

    // TODO: use dataflow to map from uses of aliases back to the underlying type
  }

  /**
   * A call to `T.self_type`.
   */
  class RbiSelfType extends RbiTypeCall {
    RbiSelfType() { this.getMethodName() = "self_type" }
  }

  /**
   * A call to `T.noreturn`.
   */
  class RbiNoreturnType extends RbiTypeCall {
    RbiNoreturnType() { this.getMethodName() = "noreturn" }
  }

  // TODO: class Foo < T::Enum

  // TODO: class Foo < T::Struct

  // TODO: inheritance?

  class ParameterType extends ExprNodes::PairCfgNode {
    private RbiType t;

    ParameterType() { t.asExpr() = this.getValue() }

    /** Gets the `RbiType` of this parameter. */
    RbiType getType() { result = t }

    private SigCall getOuterSigCall() {
      this = result.getAParamsCall().getAParameterType()
    }

    private ExprNodes::MethodBaseCfgNode getAssociatedMethod() {
      result = this.getOuterSigCall().getAssociatedMethod()
    }

    /** Gets the parameter to which this type applies. */
    NamedParameter getParameter() {
      result = this.getAssociatedMethod().getExpr().getAParameter() and
      result.getName() = this.getKey().getConstantValue().getStringlikeValue()
    }
  }

}
