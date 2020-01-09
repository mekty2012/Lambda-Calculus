package PLTImplementation

package object FirstOrderLogic extends Language {

  trait FirstOrderLogic
  case class Bool(b:Boolean) extends FirstOrderLogic
  case class Rel(rel:IntegerRelation.Value, first:IntegerExpression.IntegerExpression, second:IntegerExpression.IntegerExpression) extends FirstOrderLogic
  case class Neg(pl:FirstOrderLogic) extends FirstOrderLogic
  case class And(first:FirstOrderLogic, second:FirstOrderLogic) extends FirstOrderLogic
  case class Or(first:FirstOrderLogic, second:FirstOrderLogic) extends FirstOrderLogic
  case class Exists(x:String, body:FirstOrderLogic) extends FirstOrderLogic
  case class Forall(x:String, body:FirstOrderLogic) extends FirstOrderLogic

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

  def freeVariable(pl:FirstOrderLogic):Set[String] = pl match {
    case Bool(_) => Set()
    case Rel(_, f, s) => freeVariable(f) ++ freeVariable(s)
    case Neg(e) => freeVariable(e)
    case And(f, s) => freeVariable(f) ++ freeVariable(s)
    case Or(f, s) => freeVariable(f) ++ freeVariable(s)
    case Exists(x, b) => freeVariable(b) - x
    case Forall(x, b) => freeVariable(b) - x
  }

  def replace(pl:FirstOrderLogic, x:String, other:IntegerExpression.IntegerExpression) : FirstOrderLogic = pl match {
    case Bool(_) => pl
    case Rel(op, f, s) => Rel(op, replace(f, x, other), replace(s, x, other))
    case Neg(e) => Neg(replace(e, x, other))
    case And(f, s) => And(replace(f, x, other), replace(s, x, other))
    case Or(f, s) => Or(replace(f, x, other), replace(s, x, other))
    case Exists(x, b) => ??? // TODO
    case Forall(x, b) => ??? // TODO
  }


  /*
  object FirstOrderLogicParser extends RegexParsers {
    def parenWrap[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
    lazy val bool: Parser[Boolean] = """(true)|(false)""".r ^^ (_.toBoolean)
    
  }*/
}
