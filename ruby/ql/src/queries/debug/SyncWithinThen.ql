/**
 * @name rb/sync-within-then
 * @description todo
 * @id rb/some-query
 * @problem.severity warning
 * @kind path-problem
 */

import ruby

class SyncCall extends Ast::MethodCall {
  SyncCall() { this.getMethodName() = "sync" }
}

class ThenCall extends Ast::MethodCall {
  ThenCall() { this.getMethodName() = "then" }
}

newtype TCallPredOption =
  TCallPredNone() or
  TCallPredSome(CallWithinThen c)

/** An optional Boolean value. */
class CallPredOption extends TCallPredOption {
  string toString() {
    this = TCallPredNone() and result = "<none>"
    or
    this = TCallPredSome(any(CallWithinThen c | result = c.toString()))
  }

  CallWithinThen getCall() { this = TCallPredSome(result) }
}

class CallWithinThen extends Ast::MethodCall {
  private ThenCall tc;
  private CallPredOption pred;

  CallWithinThen() {
    tc.getBlock() = this.getEnclosingCallable() and
    pred = TCallPredNone()
    or
    exists(CallWithinThen cwt |
      cwt.getATarget() = this.getEnclosingCallable() and
      tc = cwt.getThenCall() and
      pred = TCallPredSome(cwt)
    )
  }

  ThenCall getThenCall() { result = tc }

  CallWithinThen getPred() { result = pred.getCall() }
}

query predicate edges(Ast::MethodCall a, Ast::MethodCall b) { b.(CallWithinThen).getPred() = a }

query predicate nodes(Ast::MethodCall a, string key, string val) {
  a instanceof CallWithinThen and
  key = a.toString() and
  val = a.toString()
}

predicate hasPath(CallWithinThen source, CallWithinThen sink) {
  source = sink
  or
  edges(source, sink)
  or
  exists(CallWithinThen mid |
    edges(source, mid) and
    hasPath(mid, sink)
  )
}

from CallWithinThen source, CallWithinThen sink, ThenCall tc
where
  sink instanceof SyncCall and
  not exists(source.getPred()) and
  hasPath(source, sink) and
  tc = source.getThenCall()
select sink, tc, sink, "Call to $@ from within $@", sink, sink.getMethodName(), tc,
  tc.getMethodName()
