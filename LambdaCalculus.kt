import java.lang.IllegalArgumentException

sealed class LambdaCalculus {
    abstract infix fun alphaEquiv(other:LambdaCalculus) : Boolean
}
data class Id(val name : String) : LambdaCalculus() {
    override fun toString() = name
    override fun alphaEquiv(other:LambdaCalculus) : Boolean {
        return when (other) {
            is Id -> {
                name == other.name
            }
            else -> {
                false
            }
        }
    }
}
data class App(val first:LambdaCalculus, val second:LambdaCalculus) : LambdaCalculus() {
    override fun toString() = "($first $second)"
    override fun alphaEquiv(other:LambdaCalculus) : Boolean {
        return when (other) {
            is App -> {
                first.alphaEquiv(other.first) && second.alphaEquiv(other.second)
            }
            else -> {
                false
            }
        }
    }
}
data class Lambda(val parameter : String, val body : LambdaCalculus) : LambdaCalculus() {
    override fun toString() = "l $parameter.{$body}"
    override fun alphaEquiv(other:LambdaCalculus) : Boolean {
        return when (other) {
            is Lambda -> {
                if (parameter == other.parameter) {
                    body.alphaEquiv(other.body)
                } else {
                    body.alphaEquiv(replace(other.body, other.parameter, Id(parameter)))
                }
            }
            else -> {
                false
            }
        }
    }
}

fun freeVariable(l:LambdaCalculus) : Set<String> {
    return when (l) {
        is Id -> setOf(l.name)
        is App -> freeVariable(l.first) union freeVariable(l.second)
        is Lambda -> freeVariable(l.body) - l.parameter
    }
}

/**
 *  A lambda calculus expression is (beta-)redex if it is in form
 *  (lambda x.e1) e2
 *  If lambda calculus expression is redex, it can be replaced as
 *  e1/x->e2
 */
fun isRedex(l:LambdaCalculus) : Boolean {
    return when (l) {
        is App -> {
            l.first is App
        }
        else -> false
    }
}

/**
 * A lambda calculus expression is closed if it contains no free variable.
 */
fun isClosed(l:LambdaCalculus) = isClosed(l, setOf())

fun isClosed(l:LambdaCalculus, env:Set<String>) : Boolean {
    return when (l) {
        is Id -> l.name in env
        is App -> isClosed(l.first, env) && isClosed(l.second, env)
        is Lambda -> isClosed(l.body, env + l.parameter)
    }
}

/**
 * A lambda calculus expression is normal if it contains no redex.
 */
fun isNormal(l:LambdaCalculus) : Boolean {
    return when (l) {
        is Id -> {
            true
        }
        is App -> {
            if (isRedex(l)) {
                false
            } else {
                isNormal(l.first) && isNormal(l.second)
            }
        }
        is Lambda -> {
            isNormal(l.body)
        }
    }
}

/**
 * A lambda calculus expression is canonical if can not be evaluated further.
 * In fact, we will only consider canonical form for closed expressions,
 * so the only canonical term is lambda.
 */
fun isCanonical(l:LambdaCalculus) : Boolean = l is Lambda

fun getNew(x:String, s:Set<String>):String {
    var new = x
    while (new in s) new += "'"
    return new
}

/**
 * This function computes l1/x->l2.
 * It is defined inductively as following
 * v/d = dv for Id v
 * e0 e1 / d = e0/d e1/d
 * lambda v. e / d = lambda v' (e/[d|v:v']) for v not in FV(dw) where w is in FV(lambda v. e)
 */
fun replace(l:LambdaCalculus, x:String, other:LambdaCalculus) : LambdaCalculus {
    when (l) {
        is Id -> {
            return if (l.name == x) {
                other
            } else {
                l
            }
        }
        is App -> {
            return App(replace(l.first, x, other), replace(l.second, x, other))
        }
        is Lambda -> {
            var freeVariables = freeVariable(l)
            if (x in freeVariables) {
                freeVariables = freeVariables - x
                freeVariables = freeVariables union freeVariable(other)
            }
            return if (l.parameter !in freeVariables) {
                Lambda(l.parameter, replace(l.body, x, other))
            } else {
                val paramnew = getNew(l.parameter, freeVariables)
                Lambda(paramnew, replace(replace(l.body, l.parameter, Id(paramnew)), x, other))
            }
        }
    }
}

/**
 * This function is helper function for Normal Order Reduction.
 * It changes redex (lambda x.e1) e2 into e1/x->e2.
 * Actually, this function performs both beta reduction and eta reduction.
 */
fun resolveRedex(l:LambdaCalculus) : LambdaCalculus {
    when (l) {
        is App -> when (l.first) {
            is Lambda -> {
                return replace(l.first.body, l.first.parameter, l.second)
            }
            else -> {throw IllegalArgumentException()}
        }
        else -> {throw IllegalArgumentException()}
    }
}

/**
 * Warning : This function may not terminate.
 * Non terminating example can not be checked before since it contradicts to halting problem.
 * This is evaluation of lambda calculus, where we resolve leftmost outermost redex.
 * More specifically, we resolve redex that is not contained in other redex, and one that is leftmost among them.
 */
fun normalOrderReduction(l:LambdaCalculus) : LambdaCalculus {
    var current = l
    while (true) {
        val result = normalOrderStep(current)
        if (result != null) {
            current = result
        }
        else {
            return current
        }
    }
}

/**
 * This function performs one step in normal order reduction.
 * This function resolves leftmost outermost redex.
 * More specifically, it resolve redex that is leftmost among redexes not contained in other redex.
 * If it is normal form, it returns None.
 */
fun normalOrderStep(l:LambdaCalculus) : LambdaCalculus? {
    if (isRedex(l)) {
        return resolveRedex(l)
    }
    else {
        when (l) {
            is Id -> {return null}
            is App -> {
                val firstResult = normalOrderStep(l.first)
                return if (firstResult != null) {
                    App(firstResult, l.second)
                } else {
                    val secondResult = normalOrderStep(l.second)
                    if (secondResult != null) {
                        App(l.first, secondResult)
                    } else {
                        null
                    }
                }
            }
            is Lambda -> {
                val bodyResult = normalOrderStep(l.body)
                return if (bodyResult != null) {
                    Lambda(l.parameter, bodyResult)
                } else {
                    null
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
fun normalOrderEvaluation(l:LambdaCalculus) :Lambda {
    if (!isClosed(l)) {
        throw IllegalArgumentException()
    }
    return when (l)  {
        is Id -> {throw IllegalArgumentException()}
        is App -> {
            val firstResult = normalOrderEvaluation(l.first)
            normalOrderEvaluation(replace(firstResult.body, firstResult.parameter, l.second))
        }
        is Lambda -> {
            l
        }
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
fun eagerEvaluation(l:LambdaCalculus) : Lambda {
    if (!isClosed(l)) {
        throw IllegalArgumentException()
    }
    return when (l) {
        is Id -> {throw IllegalArgumentException()}
        is App -> {
            val firstResult = eagerEvaluation(l.first)
            val secondResult = eagerEvaluation(l.second)
            eagerEvaluation(replace(firstResult.body, firstResult.parameter, secondResult))
        }
        is Lambda -> {
            l
        }
    }
}

object ChurchEncoding {
    /**
     * I will denote lambda as l from here.
     * Note that application is left-associative, meaning xyz is (xy)z.
     */

    // lx. ly. x
    val TRUE = Lambda("x", Lambda("y", Id("x"))) as LambdaCalculus
    // lx. ly. y
    val FALSE = Lambda("x", Lambda("y", Id("y"))) as LambdaCalculus
    // lb. lx. ly. byx
    val NOT = Lambda("b", Lambda("x", Lambda("y", App(App(Id("b"), Id("y")), Id("x"))))) as LambdaCalculus
    // lb. lc. lx. ly. b(cxy)y
    val AND = Lambda("b", Lambda("c", Lambda("x", Lambda("y", App(App(Id("b"), App(App(Id("c"), Id("x")), Id("y"))), Id("y")))))) as LambdaCalculus

    // lf. lx. f^n x
    fun num(n:Int) : LambdaCalculus {
        if (n < 0) {
            throw IllegalArgumentException()
        }
        var body = Id("x") as LambdaCalculus
        for (i in 0 until n) {
            body = App(Id("f"), body)
        }
        return Lambda("f", Lambda("x", body))
    }

    // ln. lf. lx. f(nfx)
    val SUCC = Lambda("n", Lambda("f", Lambda("x", App(Id("f"), App(App(Id("n"), Id("f")), Id("x")))))) as LambdaCalculus
    // ln. lx. ly. n(lz.y)x
    val ISZERO = Lambda("n", Lambda("x", Lambda("y", App(App(Id("n"), Lambda("z", Id("y"))), Id("x"))))) as LambdaCalculus
    // lm. ln. lf. lx. mf(nfx)
    val ADD = Lambda("m", Lambda("n", Lambda("f", Lambda("x", App(App(Id("m"), Id("f")), App(App(Id("n"), Id("f")), Id("x"))))))) as LambdaCalculus
    // lm. ln. lf. m(nf)
    val MULT = Lambda("m", Lambda("n", Lambda("f", App(Id("m"), App(Id("n"), Id("f")))))) as LambdaCalculus
    // lm. ln. nm
    val EXP = Lambda("m", Lambda("n", App(Id("n"), Id("m")))) as LambdaCalculus
}
