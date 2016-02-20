package org.cvogt.flow

import scala.annotation.implicitNotFound
import scala.language.higherKinds
import scala.annotation.compileTimeOnly
import scala.language.implicitConversions
import scala.language.experimental.macros

@compileTimeOnly("implementation detail of flow comprehensions. don't use yourself")
final class FlowContext private()

@implicitNotFound("Could not find a way to construct a ${Constructed} from a ${Param}. Consider defining an implicit instance of Construct[${Param}, ${Constructed}].")
class Construct[Param, Constructed](
  impl: Param => Constructed
) {
  def construct(p: Param): Constructed = impl(p)
}
object Construct extends ConstructInstances
trait ConstructInstances extends LowPriorityConstructImplicits {

  object TheOptionConstruct extends Construct[Any, Option[Any]](Some.apply)
  implicit def optionConstruct[T] = TheOptionConstruct.asInstanceOf[Construct[T, Option[T]]]

  import scala.concurrent._
  object TheFutureConstruct extends Construct[Any, Future[Any]](Future.successful)
  implicit def futureConstruct[T] = TheFutureConstruct.asInstanceOf[Construct[T, Future[T]]]

}
trait LowPriorityConstructImplicits {
  implicit def nameBasedConstruct[T, C]: Construct[T, C] =
    macro FlowMacros.nameBasedConstruct[T, C]
}

@implicitNotFound("Could not find a way to flatMap over objects of type ${CT} using functions of type ${T} => ${CU}. Consider defining an implicit instance of FlatMap[${CT}, ${T}, ${CU}]")
class FlatMap[CT, T, CU](
  impl: (CT, (T => CU)) => CU
) {
  def flatMap(ct: CT, f: T => CU): CU = impl(ct, f)
}

object FlatMap extends FlatMapInstances
trait FlatMapInstances {
  implicit def nameBasedFlatMap[CT, T, CU]: FlatMap[CT, T, CU] =
    macro FlowMacros.nameBasedFlatMap[CT, T, CU]
}

object `package` {

  object implicits{
    import scala.language.implicitConversions
    /** careful, this can lead to surprising effects */
    implicit def autoEmbed[M[_],T](m: M[T]): T = ???
  }
  @compileTimeOnly("implementation detail of flow comprehensions. don't use yourself")
  implicit class Embed[M[_],T](m: M[T]){
    @compileTimeOnly("the prefix ? operator can only be used in a flow comprehension scope such as flat{...}, flow{...}")
    def unary_? : T = ???
  }

  def flat[M[_]] = new flat[M]
  def transform[M[_]] = new transform[M]
  def show(t: Any): Unit = macro FlowMacros.show
  def gui(t: Any): Unit = macro FlowMacros.gui
  def echo[T](t: T): T = macro FlowMacros.echo[T]
}

sealed abstract class Comprehension[M[_]] {
}
final class MonadContext[M[_]]{
  /** transform the surrounding monad at this point */
  @compileTimeOnly("The MonadContext type only makes sense in a flow comprehension scope and is supposed to be removed by the macro.")
  def !(transform: M[FlowContext] => M[FlowContext]) = ???
  /** extract a value from a given Monad */
  @compileTimeOnly("The MonadContext type only makes sense in a flow comprehension scope and is supposed to be removed by the macro.")
  def ?[T](monad: M[T]): T = ???
}
class flat[M[_]] extends Comprehension[M]{
  def apply[T](comprehension: MonadContext[M] => T): M[T] = macro FlowMacros.flat[M[_],T]
}
class transform[M[_]] {
  def apply[T]
    (returnName: String)
    (transforms: String*)
    (comprehension: MonadContext[M] => M[T]): M[T] =
      macro FlowMacros.transform[M[_]]
}

import scala.reflect.macros.blackbox

class FlowMacros(val c: blackbox.Context) {
  import c.universe._
  import c.weakTypeOf
  import c.internal

  val visualizer = new Visualizer[c.type](c)
  import visualizer._

  val debug =
    sys.props.get("flat_debug_transforms").getOrElse("").split(",").toSet

  val verbose =
    sys.props.get("flat_debug_verbose") match {
      case Some("true") => true
      case _ => false
    }

  import org.cvogt.flow.transforms._

  val allTransforms = Seq[Transform](
    // ImplicitExtractions,
    // Normalize,
    RewriteExtractions
  )

  def transform[M: WeakTypeTag](returnName: Tree)(transforms: Tree*)(comprehension: Tree): Tree = {
    comprehension match {
      case q"($ctxNme: $tpe) => $body" =>
        val m = weakTypeOf[M].typeConstructor
        val returnNme = returnName match {
          case Literal(Constant(nme: String)) => TermName(nme)
          case _ => c.abort(returnName.pos, "return name must be a String literal")
        }
        transforms match {
          case Nil =>
            internal.changeOwner(body, comprehension.symbol, comprehension.symbol.owner)
          case (t@Literal(Constant(currentTransformName: String))) :: remainingTransformations =>
            def ifDebug(body: => Unit): Unit = {
              if(debug(currentTransformName)) body
              else ()
            }
            def ifVerbose(body: => Unit): Unit = {
              if (debug(currentTransformName) && verbose) body
              else ()
            }
            val ctx = new TransformContext[c.type](c) {
              val M: Type = m
              val contextName: TermName = ctxNme
              val returnName = returnNme
              def recur(t: Tree): Tree = {
                q"""
                  _root_.org.cvorg.flow.transform[$m]($returnName)(..${transforms})(($ctxNme: _root_.org.cvogt.flow.MonadContext[$m]) => $t)
                """
              }
            }
            import ctx.{returnName=>_, _}

            allTransforms.find(_.name == currentTransformName) match {
              case Some(currentTransform) =>
                ifDebug {
                  println("====================")
                  println(s"running $currentTransformName")
                  println(s"$currentTransform input:")
                  println(showCode(comprehension))
                }

                case class Step(parts: List[Int] = List(1)) {
                  def next = Step(
                    parts.init :+ (parts.last + 1)
                  )
                  def sub = Step(parts :+ 1)
                  override def toString = parts.mkString(".")
                }

                def traverse(
                  done: List[Tree],
                  remaining: List[Tree],
                  step: Step
                ): Tree = {
                  remaining match {
                    case h :: t =>
                      ifVerbose {
                        println(s"""$step - input: $h"""")
                      }
                      currentTransform.rewrites[c.type](ctx).find { rw =>
                        rw.pf.isDefinedAt(h)
                      } match {
                        case None =>
                          ifVerbose {
                            println(s"""$step - error: no matching rewrite rule"""")
                          }
                          c.abort(c.enclosingPosition, "no matching rewrite rule for "++showCode(h))
                        case Some(rw) =>
                          ifVerbose {
                            println(s"""$step - matching rule: "${rw.name}"""")
                          }
                          rw.pf(h) match {
                            case Accept =>
                              ifVerbose {
                                println(s"""$step - result: accept line""")
                              }
                              traverse(done :+ h, t, step.next)
                            case RewriteTo(replacement) =>
                              ifVerbose {
                                println(s"""$step - result: rewrite line""")
                                println(s"""$step - rewriteTo: ${showCode(replacement)}""")
                              }
                              traverse(done, replacement.shard ++ t, step.next)
                            case TransformRest(f) =>
                              ifVerbose {
                                println(s"""$step - result: recur""")
                              }
                              val input = traverse(Nil, t, step.sub)
                              val output = f(input)
                              ifVerbose {
                                println(s"""$step - transform input: ${showCode(input)}""")
                                println(s"$step - transform output: ${showCode(output)}")
                              }
                              traverse(done ++ output.shard, Nil, step.next)
                          }
                      }
                    case Nil =>
                      ifVerbose {
                        println(s"""$step - done""")
                      }
                      val result = q"""
                        _root_.org.cvogt.flow.transform[$m]($returnName)(..$remainingTransformations) {
                          ($ctxNme: _root_.org.cvogt.flow.MonadContext[$m]) => ..$done
                        }
                      """
                      c.typecheck(result)
                  }
                }

                val result = traverse(
                  Nil,
                  body.shard,
                  Step()
                )

                ifDebug {
                  println(s"$currentTransform output:")
                  println(showCode(result))
                  println("====================")
                }
                result
              case None =>
                c.abort(t.pos, "unknown transformation phase")
            }
          case other :: rest =>
            c.abort(other.pos, s"transformation phases must be identified with literal Strings")
        }
    }
  }


//   //   def doContextTransforms(next: Transformation) =
//   //     Transformation("context transform") { t =>

//   //       sealed trait ScopeOp
//   //       case class DefineVal(valDef: ValDef) extends ScopeOp
//   //       case class DefineObject(modDef: ModuleDef) extends ScopeOp
//   //       case class DefineDef(defDef: DefDef) extends ScopeOp
//   //       case class ImportSomething(imported: Import) extends ScopeOp

//   //       // For now, we'll ignore local classes and traits, but we should support them
//   //       case class DefineClass(defined: ClassDef) extends ScopeOp

//   //       def doContextTransform(
//   //         trees: List[Tree],
//   //         scopeOps: List[ScopeOp],
//   //         done: List[Tree]
//   //       ): Tree = trees match {
//   //         case Nil => next.transform(done.unify)
//   //         case (v: ValDef) :: rest if !v.mods.hasFlag(Flag.ARTIFACT) =>
//   //           doContextTransform(
//   //             rest,
//   //             scopeOps :+ DefineVal(v),
//   //             done :+ v
//   //           )
//   //         case (d: DefDef) :: rest =>
//   //           doContextTransform(
//   //             rest,
//   //             scopeOps :+ DefineDef(d),
//   //             done :+ d
//   //           )
//   //         case (m: ModuleDef) :: rest =>
//   //           doContextTransform(
//   //             rest,
//   //             scopeOps :+ DefineObject(m),
//   //             done :+ m
//   //           )
//   //         case (i: Import) :: rest =>
//   //           doContextTransform(
//   //             rest,
//   //             scopeOps :+ ImportSomething(i),
//   //             done :+ i
//   //           )
//   //         case q"""
//   //           $contextName.! { ($nme1: $tpe1) =>
//   //             $nme.$op { ..$stats; ($nme2: $tpe2) => $expr }
//   //           }
//   //         """ :: rest =>
//   //           val body = q"..$stats; $expr"
//   //           val prefix = next.transform(q"..$done")
//   //           val paramName = TermName(c.freshName("param"))
//   //           val transformed = q"$prefix.$op(($paramName: Any) => $body)"
//   //           val continued = doContextTransform(rest, Nil, Nil)
//   //           q"$transformed.flatMap { (paramName: Any) => $continued }"
//   //         case other :: rest =>
//   //           doContextTransform(
//   //             rest,
//   //             scopeOps,
//   //             done :+ other
//   //           )
//   //       }
//   //       doContextTransform(t.shard, Nil, Nil)
//   //     }



//   /** like identity but prints desugared code and tree */
//   def debugMacro(tree: Tree): Tree = {
//     println("code:\n  "+tree)
//     println("Tree:\n  "+showRaw(tree))
//     tree
//   }


  def showSym(s: Symbol) = {
    println(c.universe.show(s))
    println(c.universe.showDecl(s))
    println(showRaw(s, printIds=true, printOwners=true, printTypes=true))
    println(showRaw(s.info, printIds=true, printOwners=true, printTypes=true))
  }

  // def show(t: Tree): Tree = {
  //   println(showRaw(c.macroApplication.symbol, printIds=true, printOwners=true, printTypes=true))
  //   println(showCode(c.macroApplication, printIds=true,printOwners=true,printTypes=true,printRootPkg=true))
  //   println(showRaw(c.macroApplication, printIds=true, printOwners=true,printTypes=true))
  //   val q"$identity { $ctx => ${v@q"val $x = 3"}; $y }" = t
  //   showSym(ctx.symbol)
  //   showSym(ctx.symbol.owner)
  //   showSym(ctx.symbol.owner.owner)
  //   q"()"
  // }

  def show(t: Tree): Tree = {
    println(showCode(t, printIds=true, printOwners=true, printTypes=true))
    println(showRaw(t, printIds=true, printOwners=true, printTypes=true))
    showSym(t.symbol)
    showSym(t.symbol.owner)
    q"()"
  }

  def gui(t: Tree): Tree = {
    visualize("gui" -> t)
    q"()"
  }

  def flat[M: c.WeakTypeTag, T: c.WeakTypeTag](comprehension: Tree): Tree = {
    if (verbose) {
      println(s"got: $comprehension")
    }
    comprehension match {
      case q"($ctxParam) => $body" =>

        if (verbose) {
          println(s"transformed to: $body")
        }

        val utils = new TransformUtils[c.type](c) {
          val M = weakTypeOf[M].typeConstructor
          val contextName = ctxParam.name
        }
        import utils._

        val nonEmptyBody = body match {
          case EmptyTree =>
            val result = q"()"
            internal.setType(result, typeOf[Unit])
            result
          case nonEmpty => nonEmpty
        }

        val returnName = c.freshName("return")

        val withCorrectReturnValue =
          body.liftReturnValue(comprehension.symbol.owner, TermName(returnName))

        val function = q"""{ ($ctxParam) =>
          $withCorrectReturnValue
        }
        """
        internal.setSymbol(function, comprehension.symbol)

        val debug = sys.props.get("flat_debug").map(_.toBoolean).getOrElse(false)

        val transformNames = allTransforms.map(p => Literal(Constant(p.name)))
        val result = q"""
          _root_.org.cvogt.flow.transform[$M][${weakTypeOf[T]}](${Literal(Constant(returnName))})(..$transformNames)($function)
        """
        if (verbose) {
          println(s"transformed to: $result")
        }

        result
    }
  }

  def echo[T](t: Tree): Tree = t

  def nameBasedConstruct[Param: WeakTypeTag, Out: WeakTypeTag]: Tree = {
    val Param = weakTypeOf[Param]
    val Out = appliedType(weakTypeOf[Out], Param)
    val OutCompanion = Out.typeSymbol.companion
    c.typecheck(
      q"""
        new _root_.org.cvogt.flow.Construct[$Param, $Out]($OutCompanion.apply(_: $Param))
      """
    )
  }

  def nameBasedFlatMap[CT: WeakTypeTag, T: WeakTypeTag, CU: WeakTypeTag]: Tree = {
    val CT = weakTypeOf[CT]
    val T = weakTypeOf[T]
    val CU = weakTypeOf[CU]
    q"""
      new _root_.org.cvogt.flow.FlatMap[$CT, $T, $CU]((_: $CT).flatMap(_: ($T => $CU)))
    """
  }
}
