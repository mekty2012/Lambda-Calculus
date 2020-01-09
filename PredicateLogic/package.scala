package PLTImplementation

package object PredicateLogic extends Language {

  trait PredicateLogic
  case class Bool(b:Boolean) extends PredicateLogic
  case class Rel(rel:IntegerRelation.Value, first:IntegerExpression.IntegerExpression, second:IntegerExpression.IntegerExpression) extends PredicateLogic
  case class Neg(pl:PredicateLogic) extends PredicateLogic
  case class And(first:PredicateLogic, second:PredicateLogic) extends PredicateLogic
  case class Or(first:PredicateLogic, second:PredicateLogic) extends PredicateLogic

  object IntegerRelation extends Enumeration {
    val Eq = Value("=")
    val Neq = Value("!=")
    val Lt = Value("<")
    val Le = Value("<=")
    val Gt = Value(">")
    val Ge = Value(">=")

    def strToRel(s:String) : IntegerRelation.Value = s match {
      case "=" => Eq
      case "!=" => Neq
      case "<" => Lt
      case ">" => Gt
      case "<=" => Le
      case ">+" => Ge
      case _ => throw new LanguageException("Not a relation")
    }

    def compute(v:IntegerRelation.Value, f:Int, s:Int): Boolean = v match {
      case Eq => f == s
      case Neq => f != s
      case Lt => f < s
      case Le => f <= s
      case Gt => f > s
      case Ge => f >= s
    }
  }

  def freeVariable(pl:PredicateLogic):Set[String] = pl match {
    case Bool(_) => Set()
    case Rel(_, f, s) => freeVariable(f) ++ freeVariable(s)
    case Neg(e) => freeVariable(e)
    case And(f, s) => freeVariable(f) ++ freeVariable(s)
    case Or(f, s) => freeVariable(f) ++ freeVariable(s)
  }

  def replace(pl:PredicateLogic, x:String, other:IntegerExpression.IntegerExpression) : PredicateLogic = pl match {
    case Bool(_) => pl
    case Rel(op, f, s) => Rel(op, replace(f, x, other), replace(s, x, other))
    case Neg(e) => Neg(replace(e, x, other))
    case And(f, s) => And(replace(f, x, other), replace(s, x, other))
    case Or(f, s) => Or(replace(f, x, other), replace(s, x, other))
  }

  def evaluate(pl:PredicateLogic, env:String => Int):Boolean = pl match {
    case Bool(b) => b
    case Rel(op, f, s) => IntegerRelation.compute(op, evaluate(f, env), evaluate(s, env))
    case Neg(e) => !evaluate(e, env)
    case And(f, s) => evaluate(f, env) && evaluate(s, env)
    case Or(f, s) => evaluate(f, env) || evaluate(s, env)
  }
  /*
  object PredicateLogicParser extends RegexParsers {
    def parenWrap[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val bool: Parser[Boolean] = """(true)|(false)""".r ^^ (_.toBoolean)

  }*/
}
