/**
 * @name Sync within then
 * @description Calling sync within a promise then block may cause execution to be accidentally synchronous
 * @id rb/sync-within-then
 * @problem.severity warning
 * @kind path-problem
 */

import ruby

private class SyncCall extends Ast::MethodCall {
  SyncCall() { this.getMethodName() = "sync" }
}

private class ThenCall extends Ast::MethodCall {
  ThenCall() { this.getMethodName() = "then" }
}

private newtype TCallPredOption =
  TCallPredNone() or
  TCallPredSome(CallWithinThen c)

/** An optional Boolean value. */
private class CallPredOption extends TCallPredOption {
  string toString() {
    this = TCallPredNone() and result = "<none>"
    or
    this = TCallPredSome(any(CallWithinThen c | result = c.toString()))
  }

  CallWithinThen getCall() { this = TCallPredSome(result) }
}

private class CallWithinThen extends Ast::MethodCall {
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

query predicate edges(CallWithinThen a, CallWithinThen b) { b.getPred() = a }

query predicate nodes(CallWithinThen a, string key, string val) {
  key = "semmle.label" and val = a.toString()
}

query predicate subpaths(
  CallWithinThen arg, CallWithinThen par, CallWithinThen ret, CallWithinThen out
) {
  none()
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
select sink, source, sink, "Call to $@ from within $@", sink, sink.getMethodName(), tc,
  tc.getMethodName()
