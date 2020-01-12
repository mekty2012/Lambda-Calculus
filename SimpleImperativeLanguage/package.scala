package PLTImplementation

import scala.util.parsing.combinator.RegexParsers

package object SimpleImperativeLanguage extends Language {
  type Env = Map[String, Int]
  // Uninitialized functions are defined to be 0.

  trait SimpleImperativeLanguage
  case object Skip extends SimpleImperativeLanguage
  case class Assign(n:String, e:IntegerExpression.IntegerExpression) extends SimpleImperativeLanguage
  case class Sequential(comms:List[SimpleImperativeLanguage]) extends SimpleImperativeLanguage
  case class Conditional(cond:PredicateLogic.PredicateLogic, thenComm:SimpleImperativeLanguage, elseComm:SimpleImperativeLanguage) extends SimpleImperativeLanguage
  case class While(cond:PredicateLogic.PredicateLogic, doComm:SimpleImperativeLanguage) extends SimpleImperativeLanguage

  def interp(c:SimpleImperativeLanguage, env:Env):Env = c match {
    case Skip => env
    case Assign(n, e) => env + (n -> compute(e, (it => env.getOrElse(it, 0))))
    case Sequential(comms) => comm match {
      case Nil => env
      case commh::comml => interp(Sequential(comml), interp(commh, env))
    }
    case Conditional(c, t, e) => compute(c, env) match {
      case true => interp(t, env)
      case false => interp(e, env)
    }
    case While(cond, d) => compute(cond, env) match {
      case true => interp(c, interp(d, env))
      case false => env
    }
  }

  def interpWithCont(c:SimpleImperativeLanguage, env:Env, cont: (Env -> Env)): Env = ???
}