package org.deepdive.ddlog

import scala.collection.mutable.ListBuffer

object DeepDiveLogPartitionDeriver {

  def transform(stmt: Statement, config: DeepDiveLog.Config): Statement = stmt match {
    case s: InferenceRule       => if (s.partition != null) transform(s, config.partition) else s
    case s                      => s
  }

  def transform(stmt: InferenceRule, partition: Map[String, Int]): Statement = if (stmt.partition.isDefined) {
    var newCqBody = new ListBuffer[Body]()
    (stmt.q.bodies(0)).foreach { case body => newCqBody += body }
    newCqBody += ComparisonCond(BinaryOpExpr(VarExpr(stmt.partition.get), "%", IntConst(partition("n"))), "=", IntConst(partition("i")))
    stmt.copy (q = stmt.q.copy(bodies = List(newCqBody.toList)))
  } else stmt

  def derive(program: DeepDiveLog.Program, config: DeepDiveLog.Config): DeepDiveLog.Program = {
    var partitionProgram = new ListBuffer[Statement]()
    program.foreach {case x => {partitionProgram += transform(x, config)}}
    partitionProgram.toList
  }
}
