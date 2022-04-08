import codeql.ruby.AST
import codeql.ruby.CFG
import codeql.ruby.DataFlow
import codeql.ruby.controlflow.CfgNodes
import codeql.ruby.experimental.Rbi::Rbi

/*
from NamedParameter p, RbiType t
where parameterHasType(p, t)
select p, p.getLocation(), t, t.getLocation()
 */
/*
from SigCall s
where count(s.getAssociatedMethod()) < 1
select s, s.getLocation() // , s.getAssociatedMethod()
*/
/*
from SigCall s, ParamsCall p1, ParamsCall p2
where not p1 = p2 and p2.getSigCall() = s and p1.getSigCall() = s
select s, s.getLocation(), p1, p2
*/
/*
from SigCall s, DataFlow::Node b, int childCount
where b = s.getBlock() and childCount = count(b.asExpr().getExpr().getAChild())
select s, s.getLocation(), b, childCount
order by childCount
*/
/*
from VoidCall c
where c.getLocation().getFile().getStem() = "stripe"
select c, c.getLocation(), c.getSigCall().getLocation()
*/

from SigCall c, ParameterType t
where t = c.getAParameterType()
select c, c.getLocation(), c.getAssociatedMethod(), c.getReturnType(), t.getKey(), t.getType()