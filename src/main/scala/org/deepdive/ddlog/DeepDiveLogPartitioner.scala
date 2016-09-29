package org.deepdive.ddlog

// DeepDiveLog semantic partitioning info extractor
// See: https://docs.google.com/document/d/1SBIvvki3mnR28Mf0Pkin9w9mWNam5AA0SpIGj1ZN2c4

import scala.collection.immutable.HashMap
import scala.collection.mutable.HashSet
import scala.language.postfixOps

case class SimplifiedAtom(name: String, terms: Seq[String])
case class SimplifiedInferenceRule(name: String, variables: Seq[SimplifiedAtom])

// Compiler that takes parsed program as input and turns into a partitioning file
class DeepDiveLogPartitioner( program : DeepDiveLog.Program, config : DeepDiveLog.Config ) {
  import DeepDiveLogCompiler._

  val statements = program

  val attrNameForRelationAndPosition: Map[ Tuple2[String,Int], String ] =
    (statements collect {
      case decl: SchemaDeclaration =>
        decl.a.terms.zipWithIndex.map { case (n, i) => (decl.a.name, i) -> n }
    } flatten) toMap

  val functionDeclarationByName: Map[String, FunctionDeclaration] =
    statements collect {
      case fdecl: FunctionDeclaration => fdecl.functionName -> fdecl
    } toMap

  val schemaDeclarationByRelationName: Map[String, SchemaDeclaration] =
    statements collect {
      case decl: SchemaDeclaration => decl.a.name -> decl
    } toMap

  def isCategoricalRelation(name: String): Boolean =
    schemaDeclarationByRelationName get(name) map (_.categoricalColumns.size > 0) getOrElse(false)

  val inferenceRules = statements collect { case s: InferenceRule => s }

  val statementsByHeadName: Map[String, List[Statement]] =
    statements collect {
      case s: FunctionCallRule     => s.output -> s
      case s: ExtractionRule       => s.headName -> s
      case s: SupervisionRule      => s.headName -> s
    } groupBy(_._1) mapValues(_ map {_._2})

  val statementsByRepresentative: Map[Statement, List[Statement]] =
    statementsByHeadName map { case (name, stmts) => stmts(0) -> stmts }

  val representativeStatements : Set[Statement] =
    statementsByHeadName.values map { _(0) } toSet

  def slugify(input: String): String = {
    import java.text.Normalizer
    Normalizer.normalize(input, Normalizer.Form.NFD)
      .replaceAll("[^\\w\\s-]", "") // Remove all non-word, non-space or non-dash characters
      .replace('-', ' ')            // Replace dashes with spaces
      .trim                         // Trim leading/trailing whitespace (including what used to be leading/trailing dashes)
      .replaceAll("\\s+", "_")      // Replace whitespace (including newlines and repetitions) with underscore
      .toLowerCase                  // Lowercase the final results
  }

  def optionalIndex(idx: Int) =
    if (idx < 1) "" else s"${idx}"

  // Given an inference rule, resolve its name for the compiled inference block.
  def resolveInferenceBlockName(s: InferenceRule): String = {
    // how to map a rule to its basename
    def ruleBaseNameFor(s: InferenceRule): String =
      if (s.ruleName nonEmpty) {
        slugify(s.ruleName getOrElse "rule")
      } else {
        s"inf_${
          // function name
          s.head.function.getClass.getSimpleName.toLowerCase
        }_${
          // followed by variable names
          s.head.variables map { case t => s"${if (t.isNegated) "not_" else ""}${t.atom.name}" } mkString("_")
        }"
      }
    // find this rule's base name and all rules that share it
    val ruleBaseName = ruleBaseNameFor(s)
    val allInferenceRulesSharingHead = inferenceRules filter(ruleBaseNameFor(_) equals ruleBaseName)
    if (allInferenceRulesSharingHead.length == 1) ruleBaseName // no possible name collision
    else if (s.ruleName nonEmpty)
      sys.error(s"""@name("${s.ruleName get}") repeated ${allInferenceRulesSharingHead.length} times""")
    else {
      // keep an index after the base name to prevent collision
      s"${
        // TODO finding safe prefix for every inference rule ahead of time will be more efficient
        DeepDiveLogDesugarRewriter.findSafePrefix(ruleBaseName, inferenceRules map ruleBaseNameFor toSet)
      }${
        allInferenceRulesSharingHead indexOf s
      }"
    }
  }

  def typeArity(tp: Int, typeMap: Map[String, Int], v: SimplifiedAtom): Int = {
    (0 until v.terms.size).map({ i =>
      if (typeMap("v_" + v.name + "_arg" + i.toString + "_t") == tp) {
        1
      }
      else {
        0
      }
    }).sum
  }

  def typeArity(tp: Int, typeMap: Map[String, Int], ir: SimplifiedInferenceRule): Int = {
    val ir_arity = freeTerms(ir).toSeq.map({ t => 
      if (typeMap("f_" + ir.name + "_" + t + "_t") == tp) {
        1
      }
      else {
        0
      }
    }).sum

    val arities = Set((ir.variables.map { v => typeArity(tp, typeMap, v) }):_*) + ir_arity

    println(ir.name + " -> " + arities.toString)

    if (arities.size == 1) {
      arities.head
    }
    else {
      0
    }
  }

  def freeTerms(ir: SimplifiedInferenceRule) = {
    Set((ir.variables.flatMap { v =>
      v.terms
    }):_*)
  }

  def canPartition(tbp: Map[Int, Int], typeMap: Map[String, Int], v: SimplifiedAtom): Boolean = {
    // validate every tpe in tbp
    (tbp.forall { case (tp, a) =>
      if (a == 0) {
        true
      }
      else {
        typeArity(tp, typeMap, v) == a
      }
    })&&(
      tbp.exists { case (tp, a) => (a != 0) }
    )
  }

  def canPartition(tbp: Map[Int, Int], typeMap: Map[String, Int], ir: SimplifiedInferenceRule): Boolean = {
    // validate every tpe in tbp
    (tbp.forall { case (tp, a) =>
      if (a == 0) {
        true
      }
      else {
        typeArity(tp, typeMap, ir) == a
      }
    })&&(
      tbp.exists { case (tp, a) => (a != 0) }
    )
  }

  def candidateTypePartitions(typeMap: Map[String, Int], ir: SimplifiedInferenceRule): Set[Map[Int, Int]] = {
    val types = Set((typeMap.values.toSeq):_*).toSeq

    val typeArityMap = Map((types.flatMap { tp =>
      val tp_arity = typeArity(tp, typeMap, ir)
      if (tp_arity != 0) {
        Seq((tp -> tp_arity))
      }
      else {
        Seq()
      }
    }):_*)

    submaps(typeArityMap) - (Map())
  }

  def submaps(m: Map[Int, Int]): Set[Map[Int, Int]] = {
    if (m.size == 0) {
      Set(m)
    }
    else {
      val m_head = m.head
      val submaps_m_tail = submaps(m.tail)
      submaps_m_tail union (submaps_m_tail.map { x => x + m_head }) 
    }
  }

  def partition() = {
    val template_vars = Set((program.flatMap { s =>
      s match {
        case SchemaDeclaration(Attribute(n, _, _, _), true, _) => Seq(n);
        // case InferenceRule(_, _, _, _) => { println(s); println() }
        case _ => Seq()
      }
    }):_*)

    println(template_vars)

    val simplified_irs = program.flatMap { s =>
      s match {
        case InferenceRule(h, _, _, _) => {
          val sname = resolveInferenceBlockName(s.asInstanceOf[InferenceRule])
          val svars = h.variables.flatMap { v =>
            if (template_vars.contains(v.atom.name) && v.atom.terms.forall(t => t.isInstanceOf[VarPattern])) {
              Seq(SimplifiedAtom(v.atom.name, v.atom.terms.map(t => t.asInstanceOf[VarPattern].name)))
            }
            else {
              Seq()
            }
          }
          Seq(SimplifiedInferenceRule(sname, svars))
        }
        case _ => Seq()
      }
    }

    for (si <- simplified_irs) {
      println()
      println(si)
    }

    val arityMap = Map((template_vars.toSeq.map { v =>
      val v_arities = Set((simplified_irs.flatMap { si =>
        si.variables.flatMap { vv =>
          if (vv.name == v) {
            Seq(vv.terms.size)
          }
          else {
            Seq()
          }
        }
      }):_*)

      assert(v_arities.size == 1)

      v -> v_arities.head
    }):_*)

    println()
    println(arityMap)

    val typeUnifier = new TypeUnifier

    for (si <- simplified_irs) {
      for (v <- si.variables) {
        for ((t, i) <- v.terms.zipWithIndex) {
          typeUnifier.unify(
            "f_" + si.name + "_" + t + "_t",
            "v_" + v.name + "_arg" + i.toString + "_t"
          )
        }
      }
    }

    println()
    println(typeUnifier.typeMap)

    val candidate_partitions = Seq((simplified_irs.map({ ir =>
      candidateTypePartitions(typeUnifier.typeMap, ir)
    }).reduce(_ union _).subsets.toSeq):_*)

    println()
    println(candidate_partitions)

    println("foo")
    println("bar")
    println(candidate_partitions)

    for (type_partition <- candidate_partitions) {
      val can_distribute_var_map = Map((template_vars.toSeq.map { v =>
        v -> (type_partition.toSeq.map({ tbp => 
          if (canPartition(tbp, typeUnifier.typeMap, SimplifiedAtom(v, (0 until arityMap(v)).map { i => "" } ))) {
            1
          }
          else {
            0
          }
        }).sum == 1)
      }):_*)

      println()
      println(type_partition)
      println(can_distribute_var_map)
    }
  }

}

class TypeUnifier {
  var typeMap = Map[String, Int]()
  var nextType = 0

  def unify(x: String, y: String) {
    if (!typeMap.contains(x) && !typeMap.contains(y)) {
      typeMap ++= Seq(x -> nextType, y -> nextType)
      nextType += 1
    }
    else if (!typeMap.contains(x) && typeMap.contains(y)) {
      typeMap += (x -> typeMap(y))
    }
    else if (typeMap.contains(x) && !typeMap.contains(y)) {
      typeMap += (y -> typeMap(x))
    }
    else {
      val tx = typeMap(x)
      val ty = typeMap(y)
      if (tx != ty) {
        val tz = Math.min(tx, ty)
        typeMap = typeMap.mapValues { v =>
          if ((v == tx) || (v == ty)) {
            tz
          }
          else {
            v
          }
        }
      }
    }
  }
}

object DeepDiveLogPartitioner extends DeepDiveLogHandler {

  type CompiledBlocks = List[(String, Any)]  // TODO be more specific
  case class QuotedString(value: String)

  // some of the reserved names used in compilation
  val deepdiveViewOrderedColumnPrefix = DeepDiveLogCompiler.deepdiveViewOrderedColumnPrefix
  val deepdiveWeightColumnPrefix = DeepDiveLogCompiler.deepdiveWeightColumnPrefix
  val deepdiveVariableIdColumn = DeepDiveLogCompiler.deepdiveVariableIdColumn
  val deepdiveVariableLabelColumn = DeepDiveLogCompiler.deepdiveVariableLabelColumn
  val deepdivePrefixForVariablesIdsTable = DeepDiveLogCompiler.deepdivePrefixForVariablesIdsTable

  // entry point for partitioning
  override def run(parsedProgram: DeepDiveLog.Program, config: DeepDiveLog.Config) = {
    // don't partition if it doesn't pass all semantic checks
    DeepDiveLogSemanticChecker.run(parsedProgram, config)
    val programToPartition = parsedProgram

    // take an initial pass to analyze the parsed program
    val partitioner = new DeepDiveLogPartitioner( programToPartition, config )

    // compile the program into blocks of deepdive.conf
    val blocks = partitioner.partition()
  }

}
