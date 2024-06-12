/**
 * @name Unreachable method
 * @description Unreachable methods may represent a bug or maintainance burden.
 * @kind problem
 * @problem.severity error
 * @security-severity 7.5
 * @precision high
 * @id rb/unreachable-method
 * @tags security
 */

import ruby
import codeql.ruby.frameworks.Rails
import codeql.ruby.frameworks.ActionDispatch
import codeql.ruby.frameworks.ActionController

File getControllerFile(ActionDispatch::Routing::Route route) {
  exists(string controllerPath | route.getController() = controllerPath |
    result.getRelativePath().matches("%/controllers/" + controllerPath + "_controller.rb")
  )
}

DataFlow::MethodNode getActionMethod(ActionDispatch::Routing::Route route) {
  result.getLocation().getFile() = getControllerFile(route) and
  result.getMethodName() = route.getAction()
}

/** A Rails request handler action. */
abstract class RailsAction extends DataFlow::MethodNode { }

/** A Rails action for which we can determine a route definition. */
class RoutedRailsAction extends RailsAction {
  private ActionDispatch::Routing::Route route;

  RoutedRailsAction() { this = getActionMethod(route) }

  ActionDispatch::Routing::Route getRoute() { result = route }
}

/** A public method in a controller class that we assume to be a rails action. */
class AssumedRailsAction extends RailsAction {
  AssumedRailsAction() { this.asExpr().getExpr() instanceof ActionControllerActionMethod }
}

/*
 * In practice, all routed actions will also be assumed actions.
 * Using just routed actions could be more precise than also using assumed actions,
 * but risks more FPs due to not detecting that a method is a routed action.
 */

/** Get known names of `method`. */
string getMethodNameWithAliases(Ast::Method method) {
  result = method.getName()
  or
  exists(Ast::MethodCall aliasMethodCall |
    aliasMethodCall.getMethodName() = "alias_method" and
    aliasMethodCall
        .getArgument(1)
        .getConstantValue()
        .isStringlikeValue(getMethodNameWithAliases(method)) and
    aliasMethodCall.getArgument(0).getConstantValue().isStringlikeValue(result)
  )
}

/**
 * A method that may be called without a matching call node.
 * These are treated as entry points into the codebase from which any called method is
 * assumed to be reachable.
 */
predicate isCalledImplicitly(Ast::Callable callable) {
  callable instanceof ActionControllerActionMethod
  or
  callable = any(ActionController::Filters::FilterCall fc).getAFilterCallable()
  or
  exists(ActionController::Filters::FilterCall fc |
    // TODO: this is not scoped - any method with matching name will be marked as reachable
    fc.getKeywordArgument("if")
        .getConstantValue()
        .isStringlikeValue(getMethodNameWithAliases(callable))
    or
    // Include inline conditions
    callable = fc.getKeywordArgument("if").getExpr()
  )
  or
  callable.(Ast::Method).getName() = "initialize"
  /*
   * TODO: There is a big gap in the call graph for resolving call targets from Rails
   * template files. In the case of a call like `<%= @some_instance_variable.some_method %>`
   * from within an ERB view file, we:
   *  1. Don't resolve `@some_instance_variable` to the corresponding instance variable in the controller class
   *  2. We therefore don't have any potential type information for `@some_instance_variable`
   *  3. Consequently, `some_method` has no identified targets.
   *
   * This also applies to the common case where the reciever is `self` (implicitly or explicitly)
   * and should refer to a controller class instance.
   *
   * The only case that currently works is a call to a class method, e.g. `SomeClass.some_method` where the
   * class is directly stated and can be resolved.
   */

  }

/*
 * The callable code here uses an AST based approach to find calls that are 'reachable'
 * from a given entry point. This is not sound, in a case like:
 * ```rb
 * def foo
 *   return 7
 *   bar()
 * end
 * ```
 * the call to `bar()` is not reachable as `foo` will always return before this call.
 * Using the control-flow graph would be more accurate here.
 */

/** Gets any calls that appear syntactically within `n`. */
Ast::Call getSyntacticallyContainedCalls(Ast::AstNode n) { result = n.getAChild*() }

/**
 * Gets any calls that appear syntactially within `n`,
 * or that appear within the body of a callable which is
 * called from within `n`, recursively.
 */
Ast::Call getAllReachableCalls(Ast::AstNode n) {
  result = getSyntacticallyContainedCalls(n)
  or
  result = getAllReachableCalls(getSyntacticallyContainedCalls(n).getATarget())
}

/**
 * Gets all callables which can be reached from `n`.
 */
Ast::Callable getCalledMethods(Ast::AstNode n) { result = getAllReachableCalls(n).getATarget() }

/**
 * Holds if a call to `m` is reachable via an implicit method call.
 */
predicate isCalled(Ast::Callable m) {
  isCalledImplicitly(m)
  or
  exists(Ast::Method mPred | isCalled(mPred) | m = getCalledMethods(mPred))
}

/**
 * A method that appears to be part of production code.
 */
class ProdMethod extends Ast::Method {
  ProdMethod() {
    exists(string relPath | relPath = this.getFile().getRelativePath() |
      not (
        relPath.matches("%spec%")
        or
        relPath.matches("%test%")
      )
    )
  }
}

/** Holds if `method` does not appear to be called from a known entry-point into the codebase. */
query predicate potentiallyUnreachableMethod(ProdMethod method, string msg) {
  not isCalled(method) and
  msg = "No reachable call found for method " + method
}

/**
 * A very basic check for if there exists a method call with matching name.
 * This makes no attempt to get the scope right, so it may resolve calls to
 * methods that do not actually match the call.
 */
query predicate noCallFoundNaive(ProdMethod method, string msg) {
  not isCalledImplicitly(method) and
  not exists(Ast::MethodCall call | call.getMethodName() = getMethodNameWithAliases(method)) and
  msg = "No method call found to a method named " + method
}
