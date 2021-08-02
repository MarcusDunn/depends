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
    object TStar : InferableTerm()
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