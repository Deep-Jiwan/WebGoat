/**
 * @name SQL text built from untrusted concatenation, then passed to a JDBC prepare/execute call
 * @description The standard SQL injection query models raw `Statement.execute*(String)` as the
 *              sink and generally treats any call to `Connection.prepareStatement` as safe,
 *              because binding values through `?` placeholders is normally sufficient protection.
 *              That assumption breaks when the SQL text itself -- the string handed to
 *              `prepareStatement`/`prepareCall`, before any placeholder is bound -- is built by
 *              concatenating remote user input. The placeholders no longer protect the
 *              concatenated fragment and the query remains injectable even though a
 *              PreparedStatement is used. This query flags that variant.
 * @kind path-problem
 * @problem.severity error
 * @security-severity 9.1
 * @precision high
 * @id java/webgoat/prepared-statement-concat-injection
 * @tags security
 *       external/cwe/cwe-089
 */

import java
import semmle.code.java.dataflow.TaintTracking
import semmle.code.java.dataflow.FlowSources
import DataFlow::PathGraph

/**
 * The `sql` text argument of a call that ultimately runs a query: either the first argument to
 * `Connection.prepareStatement`/`prepareCall`, or the first argument to a `Statement.execute*`
 * call (kept as a secondary sink so this pack still catches the classic raw-Statement variant).
 */
class SqlTextArgument extends DataFlow::ExprNode {
  SqlTextArgument() {
    exists(MethodCall mc, Method m | mc.getMethod() = m and this.getExpr() = mc.getArgument(0) |
      m.getDeclaringType().getASourceSupertype*().hasQualifiedName("java.sql", "Connection") and
      m.hasName(["prepareStatement", "prepareCall"])
      or
      m.getDeclaringType().getASourceSupertype*().hasQualifiedName("java.sql", "Statement") and
      m.hasName(["execute", "executeQuery", "executeUpdate", "executeLargeUpdate", "addBatch"])
    )
  }
}

/** Only flag when the SQL text is not a plain compile-time constant, i.e. it is built dynamically. */
class DynamicSqlTextSink extends SqlTextArgument {
  DynamicSqlTextSink() { not exists(this.getExpr().(CompileTimeConstantExpr)) }
}

module ConcatSqlConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) { source instanceof RemoteFlowSource }

  predicate isSink(DataFlow::Node sink) { sink instanceof DynamicSqlTextSink }

  predicate isBarrier(DataFlow::Node node) { none() }
}

module Flow = TaintTracking::Global<ConcatSqlConfig>;

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink)
select sink.getNode(), source, sink,
  "SQL text passed to a JDBC prepare/execute call is built from $@, which defeats the safety " +
    "of any prepared-statement placeholders elsewhere in the same string.", source.getNode(),
  "user-provided input"
