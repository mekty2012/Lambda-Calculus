package PLTImplementation

import scala.util.parsing.combinator.RegexParsers

package object IntegerExpression extends Language {
  trait IntegerExpression
  case class Num(n:Int) extends IntegerExpression {
    override def toString : String = n.toString
  }
  case class Var(name:String) extends IntegerExpression {
    override def toString : String = name
  }
  case class IntOp(op:Operator.Value, first:IntegerExpression, second:IntegerExpression) extends IntegerExpression {
    override def toString : String = s"($first $op $second)"
  }

  object Operator extends Enumeration {
    val Add = Value("+")
    val Sub = Value("-")
    val Mul = Value("*")
    val Div = Value("/")
    val Rem = Value("%")

    def strToOp(s:String):Operator.Value = s match {
      case "+" => Add
      case "-" => Sub
      case "*" => Mul
      case "/" => Div
      case "%" => Rem
      case _ => throw new IllegalArgumentException("Not a operation")
    }

    def compute(op:Operator.Value, f:Int, s:Int) : Int = op match {
      case Add => f + s
      case Sub => f - s
      case Mul => f * s
      case Div => f / s
      case Rem => f % s
    }
  }

  def freeVariable(ie:IntegerExpression) : Set[String] = ie match {
    case Num(_) => Set()
    case Var(s) => Set(s)
    case IntOp(_, f, s) => freeVariable(f) ++ freeVariable(s)
  }

  def replace(ie:IntegerExpression, x:String, other:IntegerExpression) : IntegerExpression = ie match {
    case Num(_) => ie
    case Var(s) => if (s == x) other else ie
    case IntOp(op, f, s) => IntOp(op, replace(f, x, other), replace(s, x, other))
  }

  def evaluate(ie:IntegerExpression, env:String => Int):Int = ie match {
    case Num(n) => n
    case Var(s) => env(s)
    case IntOp(op, f, s) => Operator.compute(op, evaluate(f, env), evaluate(s, env))
  }

  object IntegerExpressionParser extends RegexParsers {
    def parenWrap[T](rule:Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val int: Parser[Int] = """-?\d+""".r ^^ (_.toInt)
    lazy val str: Parser[String] = """[a-zA-Z0-9-']*""".r
    lazy val op: Parser[Operator.Value] = """[-+*/%]""".r ^^ Operator.strToOp
    lazy val expr : Parser[IntegerExpression] =
      parenWrap(op ~ expr ~ expr) ^^ {case f ~ s ~ t => IntOp(f, s, t)} |
      int ^^ {(n => Num(n))} |
      str ^^ {(s => Var(s))}
  }
}

