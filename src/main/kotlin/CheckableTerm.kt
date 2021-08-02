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