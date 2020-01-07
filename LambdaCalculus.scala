import java.lang.IllegalArgumentException

import scala.util.parsing.combinator._

trait LambdaCalculus {
  def alphaEquiv(other: LambdaCalculus): Boolean
}

case class Id(name: String) extends LambdaCalculus {
  def alphaEquiv(other:LambdaCalculus): Boolean = other match {
    case Id(n) => n == name
    case _ => false
  }
  override def toString = name
}

case class App(first: LambdaCalculus, second: LambdaCalculus) extends LambdaCalculus {
  def alphaEquiv(other:LambdaCalculus): Boolean = other match {
    case App(f, s) => first.alphaEquiv(f) && second.alphaEquiv(s)
    case _ => false
  }
  override def toString = s"($first $second)"
}

case class Lambda(parameter: String, body:LambdaCalculus) extends LambdaCalculus {
  def alphaEquiv(other: LambdaCalculus): Boolean = other match {
    case Lambda(p, b) => {
      if (parameter == p) body.alphaEquiv(b)
      else body.alphaEquiv(replace(b, p, Id(parameter)))
    }
  }
  override def toString = s"l $parameter.{$body}"
}

def freeVariable(l:LambdaCalculus) : Set[String] = l match {
  case Id(n) => Set(n)
  case App(f, s) => freeVariable(f) ++ freeVariable(s)
  case Lambda(p, b) => freeVariable(b) - p
}

/**
 *  A lambda calculus expression is (beta-)redex if it is in form
 *  (lambda x.e1) e2
 *  If lambda calculus expression is redex, it can be replaced as
 *  e1/x->e2
 */
def isRedex(l:LambdaCalculus): Boolean = l match {
  case App(f, s) => f.isInstanceOf[Lambda]
  case _ => false
}

/**
 * A lambda calculus expression is closed if it contains no free variable.
 */
def isClosed(l:LambdaCalculus): Boolean = isClosed(l, Set())

def isClosed(l:LambdaCalculus, env:Set[String]) : Boolean = l match {
  case Id(n) => env.contains(n)
  case App(f, s) => isClosed(f, env) && isClosed(s, env)
  case Lambda(p, b) => isClosed(b, env + p)
}

/**
 * A lambda calculus expression is normal if it contains no redex.
 */
def isNormal(l:LambdaCalculus): Boolean = l match {
  case Id(_) => true
  case App(f, s) => (!isRedex(l)) && (isNormal(f) && isNormal(s))
  case Lambda(p, b) => isNormal(b)
}

/**
 * A lambda calculus expression is canonical if can not be evaluated further.
 * In fact, we will only consider canonical form for closed expressions,
 * so the only canonical term is lambda.
 */
def isCanonical(l:LambdaCalculus) : Boolean = l.isInstanceOf[Lambda]

def getNew(x:String, s:Set[String]):String = {
  var newString : String = x
  while (s.contains(newString)) {
    newString = newString + "'"
  }
  newString
}

/**
 * This function computes l1/x->l2.
 * It is defined inductively as following
 * v/d = dv for Id v
 * e0 e1 / d = e0/d e1/d
 * lambda v. e / d = lambda v' (e/[d|v:v']) for v not in FV(dw) where w is in FV(lambda v. e)
 */
def replace(l:LambdaCalculus, x:String, other:LambdaCalculus): LambdaCalculus = l match {
  case Id(n) =>
    if (n == x) other else l
  case App(f, s) =>
    App(replace(f, x, other), replace(s, x, other))
  case Lambda(p, b) => {
    var freeVariables = freeVariable(l)
    if (freeVariables.contains(x)) {
      freeVariables = freeVariables - x
      freeVariables = freeVariables ++ freeVariable(other)
    }
    if (freeVariables.contains(p)) {
      val newParam = getNew(p, freeVariables)
      Lambda(newParam, replace(replace(b, p, Id(newParam)), x, other))
    }
    else {
      Lambda(p, replace(b, x, other))
    }
  }
}

/**
 * This function is helper function for Normal Order Reduction.
 * It changes redex (lambda x.e1) e2 into e1/x->e2.
 * Actually, this function performs both beta reduction and eta reduction.
 */
def resolveRedex(l:LambdaCalculus): LambdaCalculus = l match {
  case App(f, s) => f match {
    case Lambda(p, b) => replace(b, p, s)
    case _ => throw new IllegalArgumentException("Expression is not a redex")
  }
  case _ => throw new IllegalArgumentException("Expression is not a redex")
}

/**
 * Warning : This function may not terminate.
 * Non terminating example can not be checked before since it contradicts to halting problem.
 * This is evaluation of lambda calculus, where we resolve leftmost outermost redex.
 * More specifically, we resolve redex that is not contained in other redex, and one that is leftmost among them.
 */
def normalOrderReduction(l:LambdaCalculus): LambdaCalculus = {
  var current : LambdaCalculus = l
  while (true) {
    val result = normalOrderStep(current)
    result match {
      case None => current
      case Some(c) => {current = c}
    }
  }
  current
}

/**
 * This function performs one step in normal order reduction.
 * This function resolves leftmost outermost redex.
 * More specifically, it resolve redex that is leftmost among redexes not contained in other redex.
 * If it is normal form, it returns None.
 */
def normalOrderStep(l:LambdaCalculus): Option[LambdaCalculus] = {
  if (isRedex(l)) {
    Some(resolveRedex(l))
  }
  else {
    l match {
      case Id(_) => None
      case App(f, s) => {
        val firstResult = normalOrderStep(f)
        firstResult match {
          case Some(fr) => Some(App(fr, s))
          case None => {
            val secondResult = normalOrderStep(s)
            secondResult match {
              case Some(sr) => Some(App(f, sr))
              case None => None
            }
          }
        }
      }
      case Lambda(p, b) => {
        val bodyResult = normalOrderStep(b)
        bodyResult match {
          case Some(br) => Some(Lambda(p, br))
          case None => None
        }
      }
    }
  }
}

/**
 * This function performs normal order evaluation.
 * The input is expected to be closed form.
 * Warning : This function may not halt.
 *
 * Normal Order Evaluation is evaluation of lambda calculus into canonical form, which is defined by following rule.
 *
 * lambda v.e -> lambda v.e
 *
 * e1 -> lambda v.e    e/v->e2 -> z
 * --------------------------------
 *             e1 e2 -> z
 */
def normalOrderEvaluation(l: LambdaCalculus): Lambda = {
  if (!isClosed(l)) {
    throw new IllegalArgumentException("Expression is not closed")
  }
  l match {
    case Id(n) => throw new IllegalArgumentException("Never happens")
    case App(f, s) => {
      val firstResult = normalOrderEvaluation(f)
      normalOrderEvaluation(replace(firstResult.body, firstResult.parameter, s))
    }
    case lam@Lambda(_, _) => lam
  }
}

/**
 * This function performs eager evaluation.
 * The input is expected to be closed form.
 * Warning : This function may not halt.
 *
 * Normal Order Evaluation is evaluation of lambda calculus into canonical form, which is defined by following rule.
 *
 * lambda v.e -> lambda v.e
 *
 * e1 -> lambda v.e    e2 -> lambda v'.e'     e/v->(lambda v'.e') -> z
 * -------------------------------------------------------------------
 *                         e1 e2 -> z
 */
def eagerEvaluation(l:LambdaCalculus) : Lambda = {
  if (!isClosed(l)) {
  throw new IllegalArgumentException("Expression is not closed")
  }
  l match {
    case Id(_) => throw new IllegalArgumentException("Expression is not closed")
    case App(f, s) => {
      val firstResult = eagerEvaluation(f)
      val secondResult = eagerEvaluation(s)
      eagerEvaluation(replace(firstResult.body, firstResult.parameter, secondResult))
    }
    case lam@Lambda(_, _) => lam
  }
}

object ChurchEncoding {
  /**
   * I will denote lambda as l from here.
   * Note that application is left-associative, meaning xyz is (xy)z.
   */

  // lx. ly. x
  val TRUE: LambdaCalculus = Lambda("x", Lambda("y", Id("x")))
  // lx. ly. y
  val FALSE: LambdaCalculus = Lambda("x", Lambda("y", Id("y")))
  // lb. lx. ly. byx
  val NOT: LambdaCalculus = Lambda("b", Lambda("x", Lambda("y", App(App(Id("b"), Id("y")), Id("x")))))
  // lb. lc. lx. ly. b(cxy)y
  val AND: LambdaCalculus = Lambda("b", Lambda("c", Lambda("x", Lambda("y", App(App(Id("b"), App(App(Id("c"), Id("x")), Id("y"))), Id("y"))))))

  // lf. lx. f^n x
  def num(n:Int) : LambdaCalculus =  {
    if (n < 0) {
    throw new IllegalArgumentException("Church Encoding only accepts natural number")
  }
    var body : LambdaCalculus = Id("x")
    for (i <- 1 to n) {
      body = App(Id("f"), body);
    }
    Lambda("f", Lambda("x", body))
  }

  // ln. lf. lx. f(nfx)
  val SUCC: LambdaCalculus = Lambda("n", Lambda("f", Lambda("x", App(Id("f"), App(App(Id("n"), Id("f")), Id("x"))))))
  // ln. lx. ly. n(lz.y)x
  val ISZERO: LambdaCalculus = Lambda("n", Lambda("x", Lambda("y", App(App(Id("n"), Lambda("z", Id("y"))), Id("x")))))
  // lm. ln. lf. lx. mf(nfx)
  val ADD: LambdaCalculus = Lambda("m", Lambda("n", Lambda("f", Lambda("x", App(App(Id("m"), Id("f")), App(App(Id("n"), Id("f")), Id("x")))))))
  // lm. ln. lf. m(nf)
  val MULT: LambdaCalculus = Lambda("m", Lambda("n", Lambda("f", App(Id("m"), App(Id("n"), Id("f"))))))
  // lm. ln. nm
  val EXP: LambdaCalculus = Lambda("m", Lambda("n", App(Id("n"), Id("m"))))
}

object LambdaCalculusParser extends RegexParsers {
  def curlyWrap[T](rule: Parser[T]): Parser[T] = "{" ~> rule <~ "}"
  def parenWrap[T](rule: Parser[T]): Parser[T] = "(" ~> rule <~ ")"
  lazy val str: Parser[String] = """[a-zA-Z0-9-']*""".r
  lazy val expr: Parser[LambdaCalculus] =
    parenWrap(expr ~ expr) ^^ {case l ~ r => App(l, r)}
    "l" ~> str ~ "." ~ curlyWrap(expr) ^^ {case s ~ _ ~ e => Lambda(s, e)}
    str ^^ (s => Id(s))
  def apply(str:String):LambdaCalculus = parseAll(expr, str).getOrElse(throw new IllegalArgumentException("Bad Syntax"))
}