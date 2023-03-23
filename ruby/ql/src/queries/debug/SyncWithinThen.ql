/**
 * @name Sync within then
 * @description Calling sync within a promise then block may cause execution to be accidentally synchronous
 * @id rb/sync-within-then
 * @problem.severity warning
 * @kind path-problem
 */

import ruby

/** A call to a method named `sync` */
private class SyncCall extends Ast::MethodCall {
  SyncCall() { this.getMethodName() = "sync" }
}

/** A call to a method named `then` */
private class ThenCall extends Ast::MethodCall {
  ThenCall() { this.getMethodName() = "then" }
}

private newtype TCallPredOption =
  TCallPredNone() or
  TCallPredSome(CallWithinThen c)

/** An optional `CallWithinThen` */
private class CallPredOption extends TCallPredOption {
  string toString() {
    this = TCallPredNone() and result = "<none>"
    or
    this = TCallPredSome(any(CallWithinThen c | result = c.toString()))
  }

  CallWithinThen getCall() { this = TCallPredSome(result) }
}

/**
 * A method call within the block passed to a `ThenCall`.
 * This includes method calls that are called transitively, i.e. may not be
 * syntactically within the then block.
 */
private class CallWithinThen extends Ast::MethodCall {
  private ThenCall tc;
  private CallPredOption pred;

  CallWithinThen() {
    tc.getBlock() = this.getEnclosingCallable() and
    pred = TCallPredNone()
    or
    exists(CallWithinThen cwt |
      cwt.getATarget() = this.getEnclosingCallable() and
      tc = cwt.getAThenCall() and
      pred = TCallPredSome(cwt)
    )
  }

  ThenCall getAThenCall() { result = tc }

  CallWithinThen getAPredecessor() { result = pred.getCall() }
}

/** Holds if there is a path of length 0 or more between `source` and `sink` in the call graph */
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

query predicate edges(CallWithinThen a, CallWithinThen b) { b.getAPredecessor() = a }

query predicate nodes(CallWithinThen a, string key, string val) {
  key = "semmle.label" and val = a.toString()
}

query predicate subpaths(
  CallWithinThen arg, CallWithinThen par, CallWithinThen ret, CallWithinThen out
) {
  none()
}

from CallWithinThen source, CallWithinThen sink, ThenCall tc
where
  sink instanceof SyncCall and
  not exists(source.getAPredecessor()) and
  hasPath(source, sink) and
  tc = source.getAThenCall()
select sink, source, sink, "Call to $@ from within $@", sink, sink.getMethodName(), tc,
  tc.getMethodName()
