/**
 * data Term↑
 * = Ann Term↓ Term↓
 * | Star
 * | Pi Term↓ Term↓
 * | Bound Int
 * | Free Name
 * | Term↑ :@: Term↓
 * | Nat
 * | NatElim Term↓ Term↓ Term↓ Term↓
 * | Zero
 * | Succ Term↓
 * | Vec Term↓ Term↓
 * | Nil Term↓
 * | Cons Term↓ Term↓ Term↓ Term↓
 * | VecElim Term↓ Term↓ Term↓ Term↓ Term↓ Term↓
 * deriving (Show,Eq)
 */
sealed class InferableTerm {
    data class Ann(val checkableTerm: CheckableTerm, val type: Type) : InferableTerm()
    data class TStar(val star: Star) : InferableTerm() {
        constructor() : this(Star.Star)
    }

    data class Pi(val input: CheckableTerm, val output: CheckableTerm) : InferableTerm()
    data class Bound(val int: Int) : InferableTerm()
    data class Free(val name: Name) : InferableTerm()
    data class App(val inferableTerm: InferableTerm, val checkableTerm: CheckableTerm) : InferableTerm()
    object Nat : InferableTerm()
    object Zero : InferableTerm()
    data class NatElim(val a: CheckableTerm, val b: CheckableTerm, val c: CheckableTerm, val d: CheckableTerm) :
        InferableTerm()

    data class Succ(val data: CheckableTerm) : InferableTerm()
    data class Vec(val a: CheckableTerm, val b: CheckableTerm) : InferableTerm()
    data class Nil(val type: CheckableTerm) : InferableTerm()
    data class Cons(
        val a: CheckableTerm,
        val b: CheckableTerm,
        val c: CheckableTerm,
        val d: CheckableTerm
    ) : InferableTerm()

    data class VecElim(
        val a: CheckableTerm,
        val b: CheckableTerm,
        val c: CheckableTerm,
        val d: CheckableTerm,
        val e: CheckableTerm,
        val f: CheckableTerm,
    ) : InferableTerm()

}

enum class Star { Star }

/**
 * data Name
 * = Global String
 * | Local Int
 * | Quote Int
 * deriving (Show, Eq)
 */
sealed class Name {
    data class Global(val string: String) : Name()
    data class Local(val int: Int) : Name()
    data class Quote(val int: Int) : Name()
}

/**
 * data Term↓
 * = Inf Term↑
 * | Lam Term↓
 * deriving (Show, Eq)
 */
sealed class CheckableTerm {
    data class Inf(val inferableTerm: InferableTerm) : CheckableTerm()
    data class Lam(val checkableTerm: CheckableTerm) : CheckableTerm()
}

/**
 * data Value
 * = VLam (Value → Value)
 * | VStar
 * | VPi Value (Value → Value)
 * | VNeutral Neutral
 * | VNat
 * | VZero
 * | VSucc Value
 */
sealed class Value {
    data class VLam(val lambda: (Value) -> Value) : Value()
    object VStar : Value()
    data class VPi(val value: Value, val lambda: (Value) -> Value) : Value()
    data class VNeutral(val neutral: Neutral) : Value()
    object VNat : Value()
    object VZero : Value()
    data class VSucc(val data: Value) : Value()
    data class VNil(val data: Value) : Value()
    data class VCons(val a: Value, val b: Value, val c: Value, val d: Value) : Value()
    data class VVec(val a: Value, val b: Value) : Value()
}

/**
 * data Neutral
 * = NFree Name
 * | NApp Neutral Value
 */
sealed class Neutral {
    data class NFree(val name: Name) : Neutral()
    data class NApp(val neutral: Neutral, val value: Value) : Neutral()
    data class NNatElem(val a: Value, val b: Value, val c: Value, val d: Neutral) : Neutral()
    data class NVecElem(val a: Value, val b: Value, val c: Value, val d: Value, val e: Value, val f: Neutral) :
        Neutral()
}

/**
 * vfree :: Name → Value
 * vfree n = VNeutral (NFree n)
 */
fun vFree(name: Name): Value {
    return Value.VNeutral(Neutral.NFree(name))
}

/**
 * type Env = [Value]
 */
typealias Env = List<Value>

/**
 * eval↑ :: Term↑ → Env → Value
 * eval↑ (Ann e ) d = eval↓ e d
 * eval↑ (Free x) d = vfree x
 * eval↑ (Bound i) d = d !! i
 * eval↑ (e :@: e′) d = vapp (eval↑ e d) (eval↓ e′ d)
 * eval↑ Star d =VStar
 * eval↑ (Pi τ τ′)d =VPi (eval↓ τ d)(λx →eval↓ τ′ (x : d))
 */
fun evalInferableTerm(checkableTerm: InferableTerm, env: Env): Value {
    return when (checkableTerm) {
        is InferableTerm.Ann -> evalCheckableTerm(checkableTerm.checkableTerm, env)
        is InferableTerm.Free -> vFree(checkableTerm.name)
        is InferableTerm.Bound -> env[checkableTerm.int]
        is InferableTerm.App -> vApp(
            evalInferableTerm(checkableTerm.inferableTerm, env),
            evalCheckableTerm(checkableTerm.checkableTerm, env)
        )
        is InferableTerm.Pi -> Value.VPi(evalCheckableTerm(checkableTerm.input, env)) { x ->
            evalCheckableTerm(
                checkableTerm.output,
                listOf(x, *env.toTypedArray())
            )
        }
        is InferableTerm.TStar -> Value.VStar
        is InferableTerm.Nat -> Value.VNat
        is InferableTerm.NatElim -> {
            val m = checkableTerm.a
            val mz = checkableTerm.b
            val ms = checkableTerm.c
            val k = checkableTerm.d
            val mzVal = evalCheckableTerm(mz, env)
            val msVal = evalCheckableTerm(ms, env)
            val rec = { kVal: Value ->
                when (kVal) {
                    is Value.VNeutral -> Value.VNeutral(
                        Neutral.NNatElem(
                            evalCheckableTerm(m, env),
                            mzVal,
                            msVal,
                            kVal.neutral
                        )
                    )
                    is Value.VSucc -> msVal
                    is Value.VZero -> mzVal
                    else -> throw RuntimeException("internal: eval natElem")
                }
            }
            rec(evalCheckableTerm(k, env))
        }
        is InferableTerm.Succ -> Value.VSucc(evalCheckableTerm(checkableTerm.data, env))
        is InferableTerm.Zero -> Value.VZero
        is InferableTerm.VecElim -> {
            val a = checkableTerm.a
            val m = checkableTerm.b
            val mn = checkableTerm.c
            val mc = checkableTerm.d
            val k = checkableTerm.e
            val xs = checkableTerm.f
            val mnVal = evalCheckableTerm(mn, env)
            val mcVal = evalCheckableTerm(mc, env)
            fun rec(kVal: Value, xsVal: Value): Value {
                return when (xsVal) {
                    is Value.VNeutral -> Value.VNeutral(
                        Neutral.NVecElem(
                            evalCheckableTerm(a, env),
                            evalCheckableTerm(m, env),
                            mnVal,
                            mcVal,
                            kVal,
                            xsVal.neutral
                        )
                    )
                    is Value.VCons -> listOf(
                        xsVal.b,
                        xsVal.c,
                        xsVal.d,
                        rec(xsVal.b, xsVal.d)
                    ).fold(mcVal) { a, b -> vApp(a, b) }
                    is Value.VNil -> mnVal
                    else -> throw RuntimeException("internal: eval vecElim")
                }
            }
            rec(evalCheckableTerm(k, env), evalCheckableTerm(xs, env))
        }
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * vapp :: Value → Value → Value
 * vapp (VLam f) v = f v
 * vapp (VNeutral n) v = VNeutral (NApp n v)
 */
fun vApp(valueV20: Value, value: Value): Value {
    return when (valueV20) {
        is Value.VLam -> valueV20.lambda(value)
        is Value.VNeutral -> Value.VNeutral(Neutral.NApp(valueV20.neutral, value))
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * eval↓ :: Term↓ → Env → Value
 * eval↓ (Inf i) d = eval↑ i d
 * eval↓ (Lam e) d = VLam (λx → eval↓ e (x : d))
 */
fun evalCheckableTerm(checkableTerm: CheckableTerm, env: Env): Value {
    return when (checkableTerm) {
        is CheckableTerm.Inf -> evalInferableTerm(checkableTerm.inferableTerm, env)
        is CheckableTerm.Lam -> Value.VLam { x ->
            evalCheckableTerm(
                checkableTerm.checkableTerm,
                listOf(x, *env.toTypedArray())
            )
        }
    }
}

/**
 * type Type = Value
 * type Context =[(Name,Type)]
 */
typealias Type = Value
typealias Context = List<Pair<Name, Type>>

/**
 * type Result α = Either String α
 */
sealed class Either<out L, out R> {
    data class Left<L>(val data: L) : Either<L, Nothing>()
    data class Right<R>(val data: R) : Either<Nothing, R>()

    inline fun <T> and_then(f: (L) -> Either<T, @UnsafeVariance R>): Either<T, R> {
        return when (this) {
            is Left -> f(this.data)
            is Right -> Right(this.data)
        }
    }
}

typealias Result<L> = Either<L, String>

///**
// * kind↓ :: Context → Type → Kind → Result ()
// * kind↓ 0 (TFree x) Star = case lookup x 0 of
// *     Just (HasKind Star) → return ()
// *     Nothing → throwError "unknown identifier"
// * kind↓ 0 (Fun κ κ′) Star = do
// *     kind↓ 0 κ Star
// *     kind↓ 0 κ′ Star
// */
//fun kindDownArrow(context: Context, type: Type, kind: Kind): Result<Unit> {
//    return when (type) {
//        is Type.TFree -> when (context.find { type.name == it.first }) {
//            null -> throw RuntimeException("unknown identifier ${type.name} in $context")
//            else -> Either.Left(Unit)
//        }
//        is Type.Fun -> {
//            when (val result = kindDownArrow(context, type.input, Kind.Star)) {
//                is Either.Left -> kindDownArrow(context, type.output, Kind.Star)
//                is Either.Right -> result
//            }
//        }
//    }
//}

/**
 * type↑0 :: Context → Term↑ → Result Type
 * type↑0 = type↑ 0
 */
fun typeUpArrowZero(context: Context, inferableTerm: InferableTerm): Result<Type> {
    return typeUpArrow(0, context, inferableTerm)
}

/**
 * type↑ :: Int →Context →Term↑ →Result Type
 * type↑ i 0 (Ann e p) = do
 *      type↓ i 0 ρ VStar
 *      let τ = eval↓ ρ []
 *      type↓ i 0 e τ
 *      return τ
 * type↑ i 0 (Free x) = case lookup x 0of
 *      Just (HasType τ)→return τ
 *      Nothing →throwError "unknown identifier"
 * type↑ i 0(e :@: e′) = do
 *      σ ← type↑ i 0e
 *      case σ of
 *          Fun τ τ′ → do
 *                  type↓ i 0e′ τ
 *                  return τ′
 *          _ → throwError "illegal application"
 */
fun typeUpArrow(i: Int, context: Context, infTerm: InferableTerm): Either<Type, String> {
    return when (infTerm) {
        is InferableTerm.Ann -> when (val r1 = typeDownArrow(i, context, infTerm.checkableTerm, Value.VStar)) {
            is Either.Left -> {
                val t = evalCheckableTerm(infTerm.checkableTerm, emptyList())
                when (val r2 = typeDownArrow(i, context, infTerm.checkableTerm, t)) {
                    is Either.Left -> Either.Left(t)
                    is Either.Right -> r2
                }
            }
            is Either.Right -> r1
        }
        is InferableTerm.App -> when (val alpha = typeUpArrow(i, context, infTerm.inferableTerm)) {
            is Either.Left -> when (alpha.data) {
                is Value.VPi -> when (val r1 = typeDownArrow(i, context, infTerm.checkableTerm, alpha.data.value)) {
                    is Either.Left -> Either.Left(
                        alpha.data.lambda(
                            evalCheckableTerm(
                                infTerm.checkableTerm,
                                emptyList()
                            )
                        )
                    )
                    is Either.Right -> r1
                }
                else -> throw RuntimeException("illegal application")
            }
            is Either.Right -> alpha
        }
        is InferableTerm.Free -> when (val info = context.find { infTerm.name == it.first }) {
            null -> throw RuntimeException("unknown identifier")
            else -> Either.Left(info.second)
        }
        is InferableTerm.Pi -> when (val r1 = typeDownArrow(i, context, infTerm.input, Value.VStar)) {
            is Either.Left -> {
                val t = evalCheckableTerm(infTerm.input, emptyList())
                when (val r2 = typeDownArrow(
                    i + 1,
                    listOf(Name.Local(i) to t, *context.toTypedArray()),
                    substituteDownArrow(0, InferableTerm.Free(Name.Local(i)), infTerm.output),
                    Value.VStar
                )) {
                    is Either.Left -> Either.Left(Value.VStar)
                    is Either.Right -> r2
                }
            }
            is Either.Right -> r1
        }
        is InferableTerm.TStar -> Either.Left(Value.VStar)
        is InferableTerm.Nat -> Either.Left(Value.VStar)
        is InferableTerm.NatElim -> {
            val m = infTerm.a
            val mz = infTerm.b
            val ms = infTerm.c
            val k = infTerm.d
            typeDownArrow(i, context, m, Value.VPi(Value.VNat) { Value.VStar }).and_then {
                val mVal = evalCheckableTerm(m, emptyList())
                typeDownArrow(i, context, mz, vApp(mVal, Value.VZero)).and_then {
                    typeDownArrow(i, context, ms, Value.VPi(Value.VNat) { l ->
                        Value.VPi(vApp(mVal, l)) {
                            vApp(mVal, Value.VSucc(l))
                        }
                    }).and_then {
                        typeDownArrow(i, context, k, Value.VNat).and_then {
                            val kVal = evalCheckableTerm(k, emptyList())
                            Either.Left(vApp(mVal, kVal))
                        }
                    }
                }
            }
        }
        is InferableTerm.Succ -> when (val r1 = typeDownArrow(i, context, infTerm.data, Value.VNat)) {
            is Either.Left -> Either.Left(Value.VNat)
            is Either.Right -> r1
        }
        is InferableTerm.Zero -> Either.Left(Value.VNat)
        is InferableTerm.Cons -> typeDownArrow(i, context, infTerm.a, Value.VStar).and_then {
            val aVal = evalCheckableTerm(infTerm.a, emptyList())
            typeDownArrow(i, context, infTerm.b, Value.VNat).and_then {
                val kVal = evalCheckableTerm(infTerm.b, emptyList())
                typeDownArrow(i, context, infTerm.c, aVal).and_then {
                    typeDownArrow(i, context, infTerm.d, Value.VVec(aVal, Value.VSucc(kVal))).and_then {
                        Either.Left(Value.VVec(aVal, (Value.VSucc(kVal))))
                    }
                }
            }
        }
        is InferableTerm.Nil -> typeDownArrow(i, context, infTerm.type, Value.VStar).and_then {
            val aVal = evalCheckableTerm(infTerm.type, emptyList())
            Either.Left(Value.VVec(aVal, Value.VZero))
        }
        is InferableTerm.Vec -> typeDownArrow(i, context, infTerm.a, Value.VStar).and_then {
            typeDownArrow(i, context, infTerm.b, Value.VNat).and_then {
                Either.Left(Value.VStar)
            }
        }
        is InferableTerm.VecElim -> typeDownArrow(i, context, infTerm.a, Value.VStar).and_then {
            val aVal = evalCheckableTerm(infTerm.a, emptyList())
            typeDownArrow(
                i,
                context,
                infTerm.b,
                Value.VPi(Value.VNat) { k -> Value.VPi(Value.VVec(aVal, k)) { Value.VStar } })
                .and_then {
                    val mVal = evalCheckableTerm(infTerm.b, emptyList())
                    typeDownArrow(
                        i,
                        context,
                        infTerm.c,
                        listOf(Value.VZero, Value.VNil(aVal)).fold(mVal) { a, b -> vApp(a, b) }).and_then {
                        typeDownArrow(i, context, infTerm.d, Value.VPi(Value.VNat) { l ->
                            Value.VPi(aVal) { y ->
                                Value.VPi(Value.VVec(aVal, l)) { ys ->
                                    Value.VPi(listOf(l, ys).fold(mVal) { a, b -> vApp(a, b) }) {
                                        listOf(Value.VSucc(l), Value.VCons(aVal, l, y, ys)).fold(mVal) { a, b ->
                                            vApp(a, b)
                                        }
                                    }
                                }
                            }
                        }).and_then {
                            typeDownArrow(i, context, infTerm.e, Value.VNat).and_then {
                                val kVal = evalCheckableTerm(infTerm.e, emptyList())
                                typeDownArrow(i, context, infTerm.f, Value.VVec(aVal, kVal)).and_then {
                                    val vsVal = evalCheckableTerm(infTerm.f, emptyList())
                                    Either.Left(listOf(kVal, vsVal).fold(mVal) { a, b -> vApp(a, b) })
                                }
                            }
                        }
                    }
                }
        }
        is InferableTerm.Bound -> throw RuntimeException("internal error")
    }
}

/**
type↓ :: Int →Context →Term↓ →Type →Result ()
type↓ i 0(Inf e) τ = do
τ′ ←type↑ i 0e
unless (τ == τ′) (throwError "type mismatch")
type↓ i 0 (Lam e) (Fun τ τ′) = type↓ (i + 1) ((Local i, HasType τ) : 0) (subst↓ 0 (Free (Local i)) e) τ′
type↓ i 0 =throwError "type mismatch"
 */
fun typeDownArrow(
    i: Int,
    context: Context,
    checkableTerm: CheckableTerm,
    type: Type
): Result<Unit> {
    return when (checkableTerm) {
        is CheckableTerm.Inf -> when (val vp = typeUpArrow(i, context, checkableTerm.inferableTerm)) {
            is Either.Left -> if (quoteZero(type) == quoteZero(vp.data)) Either.Left(Unit) else throw RuntimeException("type mismatch")
            is Either.Right -> Either.Right(vp.data)
        }
        is CheckableTerm.Lam -> {
            when (type) {
                is Value.VPi -> typeDownArrow(
                    i + 1,
                    listOf(Name.Local(i) to type.value, *context.toTypedArray()),
                    substituteDownArrow(0, InferableTerm.Free(Name.Local(i)), checkableTerm.checkableTerm),
                    type.lambda(vFree(Name.Local(i)))
                )
                else -> throw RuntimeException("type mismatch")
            }
        }
    }
}

/**
 * subst↑ :: Int → Term↑ → Term↑ → Term↑
 * subst↑ i r (Ann e τ) = Ann (subst↓ i r e)τ
 * subst↑ i r (Bound j) = if i ==  j then r else Bound j
 * subst↑ i r (Free y) = Free y
 * subst↑ i r (e :@: e′) = subst↑ i r e :@: subst↓ i r e′
 * subst↑ i r Star = Star
 * subst↑ i r (Pi τ τ′)= Pi (subst↓ i r τ)(subst↓ (i + 1) r τ′)
 */
fun substituteUpArrow(i: Int, inferableTerm: InferableTerm, infTerm: InferableTerm): InferableTerm {
    return when (infTerm) {
        is InferableTerm.Ann -> InferableTerm.Ann(
            substituteDownArrow(i, inferableTerm, infTerm.checkableTerm),
            infTerm.type
        )
        is InferableTerm.Bound -> if (infTerm.int == i) inferableTerm else InferableTerm.Bound(infTerm.int)
        is InferableTerm.Free -> InferableTerm.Free(infTerm.name)
        is InferableTerm.App -> InferableTerm.App(
            substituteUpArrow(i, inferableTerm, infTerm.inferableTerm),
            substituteDownArrow(i, inferableTerm, infTerm.checkableTerm)
        )
        is InferableTerm.Pi -> InferableTerm.Pi(
            substituteDownArrow(i, inferableTerm, infTerm.input),
            substituteDownArrow(i + 1, inferableTerm, infTerm.output)
        )
        is InferableTerm.TStar -> InferableTerm.TStar()
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * subst↓ :: Int → Term↑ → Term↓ → Term↓
 * subst↓ i r (Inf e)= Inf (subst↑ i r e)
 * subst↓ i r (Lam e)= Lam (subst↓ (i +1)r e)
 */
fun substituteDownArrow(i: Int, inferableTerm: InferableTerm, checkableTerm: CheckableTerm): CheckableTerm {
    return when (checkableTerm) {
        is CheckableTerm.Inf -> CheckableTerm.Inf(substituteUpArrow(i, inferableTerm, checkableTerm.inferableTerm))
        is CheckableTerm.Lam -> CheckableTerm.Lam(
            substituteDownArrow(
                i + 1,
                inferableTerm,
                checkableTerm.checkableTerm
            )
        )
    }
}

/**
 * quote0 :: Value → Term↓
 * quote0 = quote 0
 */
fun quoteZero(value: Value): CheckableTerm {
    return quote(0, value)
}

/**
 * quote :: Int → Value → Term↓
 * quote i (VLam f) = Lam (quote (i +1) (f (vfree (Quote i))))
 * quote i (VNeutral n) = Inf (neutralQuote i n)
 * quote i VStar = Inf Star
 * quote i (VPi v f) = Inf (Pi (quote i v) (quote (i + 1) (f (vfree (Quote i)))))
 */
fun quote(i: Int, value: Value): CheckableTerm {
    return when (value) {
        is Value.VLam -> CheckableTerm.Lam(quote(i + 1, value.lambda(vFree(Name.Quote(i)))))
        is Value.VNeutral -> CheckableTerm.Inf(neutralQuote(i, value.neutral))
        is Value.VPi -> CheckableTerm.Inf(
            InferableTerm.Pi(
                quote(i, value.value),
                (quote(i + 1, value.lambda(vFree(Name.Quote(i)))))
            )
        )
        is Value.VStar -> CheckableTerm.Inf(InferableTerm.TStar())
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * neutralQuote :: Int → Neutral → Term↑
 * neutralQuote i (NFree x) = boundfree i x
 * neutralQuote i (NApp n v) = neutralQuote i n :@: quote i v
 */
fun neutralQuote(i: Int, neutral: Neutral): InferableTerm {
    return when (neutral) {
        is Neutral.NApp -> InferableTerm.App(neutralQuote(i, neutral.neutral), quote(i, neutral.value))
        is Neutral.NFree -> boundFree(i, neutral.name)
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * boundfree :: Int →Name →Term↑
 * boundfree i (Quote k)=Bound (i −k −1)
 * boundfree i x = Free x
 */
fun boundFree(i: Int, name: Name): InferableTerm {
    return when (name) {
        is Name.Quote -> InferableTerm.Bound(i - name.int - 1)
        else -> InferableTerm.Free(name)
    }
}

fun main() {

}