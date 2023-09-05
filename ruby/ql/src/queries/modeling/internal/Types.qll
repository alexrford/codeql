private import ruby
private import codeql.ruby.ApiGraphs
private import Util as Util

module Types {
  /**
   * Holds if `(type,path)` evaluates to the given method, when evalauted from a client of the current library.
   */
  private predicate pathToMethod(DataFlow::MethodNode method, string type, string path) {
    method.getLocation().getFile() instanceof Util::RelevantFile and
    exists(DataFlow::ModuleNode mod, string methodName |
      method = mod.getOwnInstanceMethod(methodName) and
      if methodName = "initialize"
      then (
        type = mod.getQualifiedName() + "!" and
        path = "Method[new]"
      ) else (
        type = mod.getQualifiedName() and
        path = "Method[" + methodName + "]"
      )
      or
      method = mod.getOwnSingletonMethod(methodName) and
      type = mod.getQualifiedName() + "!" and
      path = "Method[" + methodName + "]"
    )
  }

  /**
   * Holds if `(type,path)` evaluates to a value corresponding to `node`, when evaluated from a client of the current library.
   */
  private predicate pathToNode(API::Node node, string type, string path, boolean isOutput) {
    exists(DataFlow::MethodNode method, string prevPath | pathToMethod(method, type, prevPath) |
      isOutput = true and
      node = method.getAReturnNode().backtrack() and
      path = prevPath + ".ReturnValue" and
      not method.getMethodName() = "initialize" // ignore return value of initialize method
      or
      isOutput = false and
      (
        exists(int n |
          node = method.getParameter(n).track() and
          path = prevPath + ".Argument[" + n + "]"
        )
        or
        exists(string name |
          node = method.getKeywordParameter(name).track() and
          path = prevPath + ".Argument[" + name + ":]"
        )
        or
        node = method.getBlockParameter().track() and
        path = prevPath + ".Argument[block]"
      )
    )
    or
    exists(API::Node prevNode, string prevPath, boolean prevIsOutput |
      pathToNode(prevNode, type, prevPath, prevIsOutput)
    |
      node = prevNode.getAnElement() and
      path = prevPath + ".Element" and
      isOutput = prevIsOutput
      or
      node = prevNode.getReturn() and
      path = prevPath + ".ReturnValue" and
      isOutput = prevIsOutput
      or
      prevIsOutput = false and
      isOutput = true and
      (
        exists(int n |
          node = prevNode.getParameter(n) and
          path = prevPath + ".Parameter[" + n + "]"
        )
        or
        exists(string name |
          node = prevNode.getKeywordParameter(name) and
          path = prevPath + ".Parameter[" + name + ":]"
        )
        or
        node = prevNode.getBlock() and
        path = prevPath + ".Parameter[block]"
      )
    )
  }

  /**
   * Holds `node` should be seen as having the given `type`.
   */
  private predicate valueHasTypeName(DataFlow::LocalSourceNode node, string type) {
    node.getLocation().getFile() instanceof Util::RelevantFile and
    exists(DataFlow::ModuleNode mod |
      (
        node = mod.getAnImmediateReference().getAMethodCall("new")
        or
        node = mod.getAnOwnInstanceSelf()
      ) and
      type = mod.getQualifiedName()
      or
      (
        node = mod.getAnImmediateReference()
        or
        node = mod.getAnOwnModuleSelf()
      ) and
      type = mod.getQualifiedName() + "!"
    )
  }

  /**
   * Holds if the given type-model tuple should be emitted.
   */
  predicate typeModel(string type1, string type2, string path) {
    exists(API::Node node |
      valueHasTypeName(node.getAValueReachingSink(), type1) and
      pathToNode(node, type2, path, true)
    )
  }
}
