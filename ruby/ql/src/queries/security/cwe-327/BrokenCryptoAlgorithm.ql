/**
 * @name Use of a broken or weak cryptographic algorithm
 * @description Using broken or weak cryptographic algorithms can compromise security.
 * @kind path-problem
 * @problem.severity warning
 * @security-severity 7.5
 * @precision high
 * @id rb/weak-cryptographic-algorithm
 * @tags security
 *       external/cwe/cwe-327
 */

import codeql.ruby.AST
import codeql.ruby.DataFlow
import codeql.ruby.security.BrokenCryptoAlgorithmQuery
import codeql.ruby.security.SensitiveActions
import codeql.ruby.Concepts
import DataFlow::PathGraph

from Configuration cfg, DataFlow::PathNode source, DataFlow::PathNode sink
where
  cfg.hasFlowPath(source, sink) and
  not source.getNode() instanceof CleartextPasswordExpr // TODO: should be flagged by rb/insufficient-password-hash
select sink.getNode(), source, sink, "A broken or weak cryptographic algorithm depends on $@.",
  source.getNode(), "sensitive data from " + source.getNode().(Source).describe()
