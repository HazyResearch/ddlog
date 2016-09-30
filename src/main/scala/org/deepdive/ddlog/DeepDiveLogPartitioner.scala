package org.deepdive.ddlog

// DeepDiveLog semantic partitioning info extractor
// See: https://docs.google.com/document/d/1SBIvvki3mnR28Mf0Pkin9w9mWNam5AA0SpIGj1ZN2c4

import scala.collection.immutable.HashMap
import scala.collection.mutable.HashSet
import scala.language.postfixOps

case class SimplifiedAtom(name: String, terms: Seq[String])
case class SimplifiedInferenceRule(name: String, variables: Seq[SimplifiedAtom])

sealed trait PartitionClass

case class PartitionClassMaster(c: String) extends PartitionClass {
  override def toString() = {
    c
  }
}

case class PartitionClassWorker(c: String, by_terms: Set[String]) extends PartitionClass {
  override def toString() = {
    c + "[" + by_terms.toSeq.sorted.mkString(",") + "]"
  }
}


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

  def getVariableOwner(tbp: Map[Int, Int], typeMap: Map[String, Int], v: SimplifiedAtom): PartitionClass = {
    if (tbp.size == 0) {
      PartitionClassMaster("A")
    }
    else {
      val terms_by_type = v.terms.zipWithIndex.groupBy { case (t, i) => 
        typeMap("v_" + v.name + "_arg" + i.toString + "_t")
      }

      if (tbp.keys.forall { tp => tbp(tp) == terms_by_type(tp).size }) {
        PartitionClassWorker("C", Set(((tbp.keys.flatMap { tp =>
          terms_by_type(tp).map { case (t, i) => t }
        }).toSeq):_*))
      }
      else {
        PartitionClassMaster("A")
      }
    }
  }

  def getVariableOwner(tbps: Set[Map[Int, Int]], typeMap: Map[String, Int], v: SimplifiedAtom): PartitionClass = {
    val possible_owners = tbps.map { tbp =>
      getVariableOwner(tbp, typeMap, v)
    }

    if (possible_owners.size == 1) {
      possible_owners.head
    }
    else {
      PartitionClassMaster("A")
    }
  }

  def getFactorPartition(tbps: Set[Map[Int, Int]], typeMap: Map[String, Int], ir: SimplifiedInferenceRule, shared_vars: scala.collection.mutable.Set[String]): PartitionClass = {
    val variable_owners = Set((ir.variables.map { v =>
      getVariableOwner(tbps, typeMap, v)
    }):_*)

    if (variable_owners.size == 1) {
      // all the variables have the same local partition, so we can just use it
      variable_owners.head
    }
    else if ((variable_owners - PartitionClassMaster("A")).size == 1) {
      // the variables are all owned by either master, or a single worker
      // use partition class F
      val worker_pc = (variable_owners - PartitionClassMaster("A")).head

      for (v <- ir.variables) {
        shared_vars += v.name
      }

      PartitionClassWorker("F", worker_pc.asInstanceOf[PartitionClassWorker].by_terms)
    }
    else {
      PartitionClassMaster("H")
    }
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

  def formatTypePartition(tbps: Set[Map[Int, Int]]) = {
    tbps.toSeq.map({ tbp =>
      "(" + (tbp.keys.toSeq.sorted.flatMap({ t =>
        (0 until tbp(t)).map( i => t.toString )
      }).mkString(",")) + ")"
    }).mkString(" ")
  }

  def prefixSQL() = {
    var acc = "DROP FUNCTION IF EXISTS hash_to_bigint(text);\n"
    acc += "DROP FUNCTION IF EXISTS bigint_to_workerid(bigint);\n"
    acc += "CREATE FUNCTION hash_to_bigint(text) RETURNS bigint AS $$ "
    acc += "SELECT ('x'||substr(md5($1),1,16))::bit(64)::bigint; "
    acc += "$$ LANGUAGE SQL;\n"
    acc += "CREATE FUNCTION bigint_to_workerid(bigint) returns integer as $$ "
    acc += "SELECT MOD(24 + MOD($1, 24), 24); "
    acc += "$$ LANGUAGE SQL;"
    
    acc
  }

  def variableApplySQL(v: String, pc: PartitionClass) = {
    val table_name = "dd_variables_" + v

    var acc = s"ALTER TABLE $table_name ADD partition_key varchar(16);\n" 

    pc match {
      case PartitionClassMaster(c) => {
        acc += s"UPDATE $table_name SET partition_key = '$c';"
      }
      case PartitionClassWorker(c, ts) => {
        acc += s"UPDATE $table_name SET partition_key = '$c' || bigint_to_workerid("
        acc += ts.map({ t => "hash_to_bigint(" + t + "::text)" }).mkString(" + ")
        acc += ");"
      }
    }

    acc
  }

  def factorApplySQL(ir: SimplifiedInferenceRule, pc: PartitionClass, vm: Map[String, SimplifiedAtom]) = {
    val table_name = "dd_factors_" + ir.name

    var acc = s"ALTER TABLE $table_name ADD partition_key varchar(16);\n" 

    pc match {
      case PartitionClassMaster(c) => {
        acc += s"UPDATE $table_name SET partition_key = '$c';"
      }
      case PartitionClassWorker(c, ts) => {

        val term_map = Map((ts.toSeq.map({ t => 
          t -> ir.variables.zipWithIndex.flatMap({ case (v, i) =>
            v.terms.zip(vm(v.name).terms).map({ case (t, mt) =>
              "R" + i.toString + "." + mt
            })
          }).head
        })):_*)

        acc += s"UPDATE $table_name AS T SET partition_key = '$c' || bigint_to_workerid("
        acc += ts.map({ t => "hash_to_bigint(" + term_map(t) + "::text)" }).mkString(" + ")
        acc += ") FROM "
        acc += ir.variables.zipWithIndex.map({ case (v, i) =>
          "dd_variables_" + v.name + " AS R" + i.toString
        }).mkString(", ")
        acc += " WHERE "
        acc += ir.variables.zipWithIndex.flatMap({ case (v, i) =>
          v.terms.zip(vm(v.name).terms).map({ case (t, mt) =>
            "(R" + i.toString + "." + mt + " == " + term_map(t) + ")"
          }) :+ ("(T." + v.name + ".R" + i.toString + ".dd_id == R" + i.toString + ".dd_id)")
        }).mkString(" AND ")
        acc += ";"
      }
    }

    acc
  }

  def partition() = {
    val template_vars = Set((program.flatMap { s =>
      s match {
        case SchemaDeclaration(Attribute(n, t, _, _), true, _) => Seq(SimplifiedAtom(n, t));
        // case InferenceRule(_, _, _, _) => { println(s); println() }
        case _ => Seq()
      }
    }):_*)

    val template_var_map = Map(template_vars.toSeq.map({ v => v.name -> v }):_*)

    val template_var_names = template_vars.map { v => v.name }

    // println(template_vars)
    // println(template_var_names)

    val simplified_irs = program.flatMap { s =>
      s match {
        case InferenceRule(h, _, _, _) => {
          val sname = resolveInferenceBlockName(s.asInstanceOf[InferenceRule])
          val svars = h.variables.flatMap { v =>
            if (template_var_names.contains(v.atom.name) && v.atom.terms.forall(t => t.isInstanceOf[VarPattern])) {
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

    // for (si <- simplified_irs) {
    //   println()
    //   println(si)
    // }

    val arityMap = Map((template_var_names.toSeq.map { v =>
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

    // println()
    // println(arityMap)

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

    // println()
    // println(typeUnifier.typeMap)

    val candidate_partitions = Seq((simplified_irs.map({ ir =>
      candidateTypePartitions(typeUnifier.typeMap, ir)
    }).reduce(_ union _).subsets.toSeq):_*)

    // println()
    // println(candidate_partitions)

    // println("foo")
    // println("bar")
    // println(candidate_partitions)

    println("[")

    println(candidate_partitions.map({ type_partition =>

      val variable_owners = Map((template_vars.toSeq.map { v =>
       v -> getVariableOwner(type_partition, typeUnifier.typeMap, v)
      }):_*)

      // println()
      // println(type_partition)
      // println(variable_owners)

      val shared_vars = scala.collection.mutable.Set[String]()

      val factor_partitions = Map((simplified_irs.map { ir =>
        ir -> getFactorPartition(type_partition, typeUnifier.typeMap, ir, shared_vars)
      }):_*)

      // println(factor_partitions)

      val variable_partitions = variable_owners.map {case (v, p) =>
        v.name -> (
          if (shared_vars.contains(v.name)) {
            p match {
              case PartitionClassMaster("A") => PartitionClassMaster("B")
              case PartitionClassWorker("C", t) => PartitionClassWorker("D", t)
              case _ => throw new Exception("Unexpected partition class: " + v.toString)
            }
          }
          else {
            p
          }
        )
      }

      // println(variable_partitions)

      var acc = ""

      acc += "  {\n"

      acc += "    \"partition_types\": \"" + formatTypePartition(type_partition) + "\",\n"

      acc += "    \"variable_partition_classes\": {\n"
      acc += (variable_partitions.map({ case (v,p) =>
        "      \"" + v + "\": \"" + p.toString + "\""
      }).mkString(",\n")) + "\n"
      acc += "    },\n"

      acc += "    \"factor_partition_classes\": {\n"
      acc += (factor_partitions.map({ case (ir,p) =>
        "      \"" + ir.name + "\": \"" + p.toString + "\""
      }).mkString(",\n")) + "\n"
      acc += "    },\n"

      acc += "    \"sql_to_apply\": [\n"
      acc += ((prefixSQL.split("\n") ++
      variable_partitions.flatMap({ case (v,p) =>
        variableApplySQL(v, p).split("\n")
      }) ++ factor_partitions.flatMap({ case (ir,p) =>
        factorApplySQL(ir, p, template_var_map).split("\n")
      })).map({ s =>
        "      \"" + s + "\"" 
      }).mkString(",\n")) + "\n"
      acc += "    ]\n"

      acc += "  }"

      acc

    }).mkString(",\n"))

    println("]")
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
