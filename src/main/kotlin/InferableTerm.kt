/**
 * data Term↑
 * = Ann Term↓ Type
 * | Bound Int
 * | Free Name
 * | Term↑ :@: Term↓
 * deriving (Show, Eq)
 */
sealed class InferableTerm {
    data class Ann(val checkableTerm: CheckableTerm, val type: Type) : InferableTerm()
    data class Bound(val int: Int) : InferableTerm()
    data class Free(val name: Name) : InferableTerm()
    data class App(val inferableTerm: InferableTerm, val checkableTerm: CheckableTerm) : InferableTerm()
}

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
 * data Type
 * =TFree Name
 * | Fun Type Type
 * deriving (Show, Eq)
 */
sealed class Type {
    data class TFree(val name: Name) : Type()
    data class Fun(val input: Type, val output: Type) : Type()
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
 * | VNeutral Neutral
 */
sealed class Value {
    data class VLam(val lambda: (Value) -> Value) : Value()
    data class VNeutral(val neutral: Neutral) : Value()
}

/**
 * data Neutral
 * = NFree Name
 * | NApp Neutral Value
 */
sealed class Neutral {
    data class NFree(val name: Name) : Neutral()
    data class NApp(val neutral: Neutral, val value: Value) : Neutral()
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
    }
}

/**
 * vapp :: Value → Value → Value
 * vapp (VLam f) v = f v
 * vapp (VNeutral n) v = VNeutral (NApp n v)
 */
fun vApp(value0: Value, value: Value): Value {
    return when (value0) {
        is Value.VLam -> value0.lambda(value)
        is Value.VNeutral -> Value.VNeutral(Neutral.NApp(value0.neutral, value))
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
 * data Kind = Star
 * deriving (Show)
 */
enum class Kind {
    Star
}

/**
 * data Info
 * = HasKind Kind
 * | HasType Type
 * deriving (Show)
 */
sealed class Info {
    data class HasKind(val kind: Kind) : Info()
    data class HasType(val type: Type) : Info()
}

/**
 * type Context = [(Name, Info)]
 */
typealias Context = List<Pair<Name, Info>>

/**
 * type Result α = Either String α
 */
sealed class Either<out L, out R> {
    data class Left<L>(val data: L) : Either<L, Nothing>()
    data class Right<R>(val data: R) : Either<Nothing, R>()
}

typealias Result<L> = Either<L, String>

/**
 * kind↓ :: Context → Type → Kind → Result ()
 * kind↓ 0 (TFree x) Star = case lookup x 0 of
 *     Just (HasKind Star) → return ()
 *     Nothing → throwError "unknown identifier"
 * kind↓ 0 (Fun κ κ′) Star = do
 *     kind↓ 0 κ Star
 *     kind↓ 0 κ′ Star
 */
fun kindDownArrow(context: Context, type: Type, kind: Kind): Result<Unit> {
    return when (type) {
        is Type.TFree -> when (context.find { type.name == it.first }) {
            null -> throw RuntimeException("unknown identifier ${type.name} in $context")
            else -> Either.Left(Unit)
        }
        is Type.Fun -> {
            when (val result = kindDownArrow(context, type.input, Kind.Star)) {
                is Either.Left -> kindDownArrow(context, type.output, Kind.Star)
                is Either.Right -> result
            }
        }
    }
}

/**
 * type↑0 :: Context → Term↑ → Result Type
 * type↑0 = type↑ 0
 */
fun typeUpArrowZero(context: Context, inferableTerm: InferableTerm): Result<Type> {
    return typeUpArrow(0, context, inferableTerm)
}

/**
 * type↑ :: Int →Context →Term↑ →Result Type
 * type↑ i 0 (Ann e τ) = do
 *      kind↓ 0 τ Star
 *      type↓ i 0 e τ
 *      return τ
 * type↑ i 0(Free x) = case lookup x 0of
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
fun typeUpArrow(i: Int, context: List<Pair<Name, Info>>, infTerm: InferableTerm): Either<Type, String> {
    return when (infTerm) {
        is InferableTerm.Ann -> when (val r = kindDownArrow(context, infTerm.type, Kind.Star)) {
            is Either.Left -> when (val r1 = typeDownArrow(i, context, infTerm.checkableTerm, infTerm.type)) {
                is Either.Left -> Either.Left(infTerm.type)
                is Either.Right -> r1
            }
            is Either.Right -> r
        }
        is InferableTerm.App -> when (val alpha = typeUpArrow(i, context, infTerm.inferableTerm)) {
            is Either.Left -> when (alpha.data) {
                is Type.Fun -> when (val r = typeDownArrow(i, context, infTerm.checkableTerm, alpha.data.input)) {
                    is Either.Left -> Either.Left(alpha.data.output)
                    is Either.Right -> r
                }
                else -> throw RuntimeException("illegal application")
            }
            is Either.Right -> alpha
        }
        is InferableTerm.Free -> when (val info = context.find { infTerm.name == it.first }) {
            null -> throw RuntimeException("unknown identifier")
            else -> when (val snd = info.second) {
                is Info.HasType -> Either.Left(snd.type)
                else -> throw RuntimeException("unknown identifier")
            }
        }
        else -> throw RuntimeException("was not addressed in the haskell, assuming meant to throw")
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
    context: List<Pair<Name, Info>>,
    checkableTerm: CheckableTerm,
    type: Type
): Result<Unit> {
    return when (checkableTerm) {
        is CheckableTerm.Inf -> when (val t = typeUpArrow(i, context, checkableTerm.inferableTerm)) {
            is Either.Left -> if (t != type) Either.Left(Unit) else throw RuntimeException("type mismatch")
            is Either.Right -> t
        }
        is CheckableTerm.Lam -> {
            when (type) {
                is Type.Fun -> typeDownArrow(
                    i + 1,
                    listOf(Pair(Name.Local(i), Info.HasType(type.input)), *context.toTypedArray()),
                    substituteDownArrow(0, InferableTerm.Free(Name.Local(i)), checkableTerm.checkableTerm),
                    type.output
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
 */
fun quote(i: Int, value: Value): CheckableTerm {
    return when (value) {
        is Value.VLam -> CheckableTerm.Lam(quote(i + 1, value.lambda(vFree(Name.Quote(i)))))
        is Value.VNeutral -> CheckableTerm.Inf(neutralQuote(i, value.neutral))
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