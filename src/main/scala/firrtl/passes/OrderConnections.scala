// See LICENSE for license details.

package firrtl
package passes

import firrtl.Mappers._
import firrtl.ir._
import firrtl.Utils._
import firrtl.WrappedExpression._

import scala.collection.mutable

/** This pass replaces wires with nodes and reorders the nodes in in a legal,
  *  flow-forward ordering It must run after LowerTypes because Aggregate-type
  *  wires have multiple connections that may be impossible to order in a
  *  flow-foward way
  */
// TODO for this PR (not just this pass)
//  - Wires that are IsInvalid turn into a node with ValidIf(false,...)
//    - Should ValidIf be implemented differently in the emitter? For now it just goes away
//  - Add connects to the node ordering
//  - Preserve source locators
//  - Pattern match to put Dshlw and Shlw in for Verilog emission
//    - Is this actually a problem?
//  - Wires in Attach are kept, should they be removed?
//    - Currently Analog wires can't do anything but connect to other Wires
object OrderConnections extends Pass {
  // Extract all referential expressions from a possibly nested expression
  // TODO could this be generalized by supporting WSubAccess (which is both a reference and nested)?
  private def extractRefs(expr: Expression): Seq[Expression] = {
    val refs = mutable.ArrayBuffer.empty[Expression]
    def rec(e: Expression): Expression = {
      e match {
        case expr @ (_: WRef | _: WSubField | _: WSubIndex) => refs += expr
        case nested @ (_: Mux | _: DoPrim | _: ValidIf) => nested map rec
        case ignore @ (_: Literal) => // Do nothing
        case unexpected => throwInternalError
      }
      e
    }
    rec(expr)
    refs
  }

  // TODO Replace with deterministic digraph
  private def deterministicTopologicalSort(
      nodes: mutable.LinkedHashMap[WrappedExpression, WrappedExpression]): Seq[WrappedExpression] = {
    def getEdges(n: WrappedExpression): Seq[WrappedExpression] = extractRefs(nodes(n).e1).map(we(_))
    // Code taken from graph/DiGraph.scala
    // permanently marked nodes are implicitly held in order
    val order = new mutable.ArrayBuffer[WrappedExpression]
    // invariant: no intersection between unmarked and tempMarked
    val unmarked = nodes.clone
    val tempMarked = new mutable.LinkedHashSet[WrappedExpression]

    def visit(n: WrappedExpression): Unit = {
      if (tempMarked.contains(n)) {
        throw new Exception("Uncaught cyclic graph")
      }
      if (unmarked.contains(n)) {
        tempMarked += n
        unmarked -= n
        for (m <- getEdges(n)) {
          visit(m)
        }
        tempMarked -= n
        order.append(n)
      }
    }

    while (!unmarked.isEmpty) {
      // We just want the key. We can't just use the keys of nodes because of
      //    https://issues.scala-lang.org/browse/SI-9594
      visit(unmarked.head._1)
    }

    order
  }
  // Logic is Nodes and Connections to Wires
  private def getOrderedLogic(
      netlist: mutable.LinkedHashMap[WrappedExpression, WrappedExpression]): Seq[Statement] = {
    val sorted = deterministicTopologicalSort(netlist)
    sorted.map(we => we.e1 match {
      // Since this is after LowerTypes, Nodes and Wires can only be WRefs
      case WRef(name, _, NodeKind | ExpKind, _) => DefNode(NoInfo, name, netlist(we).e1)
      case WRef(name, _, WireKind, _) => Connect(NoInfo, we.e1, netlist(we).e1)
      case other => throwInternalError
    })
  }

  private def onModule(m: DefModule): DefModule = {
    // Store all non-node declarations here (like reg, inst, and mem)
    val decls = mutable.ArrayBuffer.empty[Statement]
    // Store all "other" statements here, non-wire, non-node connections, printfs, etc.
    val otherStmts = mutable.ArrayBuffer.empty[Statement]
    // Add nodes and wire connection here
    val netlist = mutable.LinkedHashMap.empty[WrappedExpression, WrappedExpression]


    def onStmt(stmt: Statement): Statement = {
      stmt match {
        case DefNode(_, name, expr) =>
          netlist(we(WRef(name))) = we(expr)
        case wire: DefWire =>
          decls += wire
        case decl: IsDeclaration => // Other than nodes and wires
          decls += decl
        case con: Connect => kind(con.loc) match {
          case WireKind =>
            netlist(we(con.loc)) = we(con.expr)
          case _ => otherStmts += con
        }
        case invalid: IsInvalid =>
          val ref = invalid.expr
          kind(ref) match {
            case WireKind =>
              val width = ref.tpe match { case GroundType(width) => width } // LowFirrtl
              netlist(we(ref)) = ValidIf(Utils.zero, UIntLiteral(BigInt(0), width), ref.tpe)
            case _ => otherStmts += invalid
          }
        case attach: Attach =>
          // Any wires present in an attach get readded
          // TODO should we remove these? Perhaps a CSE or ConstProp?
          attach.exprs.foreach(expr => kind(expr) match {
            case WireKind =>
              val wref = expr match { case ref: WRef => ref }
              decls += DefWire(NoInfo, wref.name, wref.tpe)
            case _ => // do nothing
          })
          otherStmts += attach
        case other @ (_: Print | _: Stop) =>
          otherStmts += other
        case EmptyStmt =>
        case block: Block => block map onStmt
      }
      stmt
    }
    m match {
      case Module(info, name, ports, body) =>
        onStmt(body)
        val logic = getOrderedLogic(netlist)
        //println(nodes.map(_.serialize).mkString("  ", "\n  ", ""))
        Module(info, name, ports, Block(decls ++ logic ++ otherStmts))
      case m: ExtModule => m
    }
  }
  def run(c: Circuit): Circuit = {
    //println(" ***** Before ***** ")
    //println(c.serialize)
    val res = Circuit(c.info, c.modules.map(onModule), c.main)
    //println(" ***** After ***** ")
    //println(res.serialize)
    //throw new Exception("bail")
    res
  }
}
