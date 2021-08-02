/**
 * type Result α = Either String α
 */
sealed class Either<out L, out R> {
    data class Left<L>(val data: L) : Either<L, Nothing>()
    data class Right<R>(val data: R) : Either<Nothing, R>()

    /**
     * allows more direct translation of `do`
     */
    inline fun <T> andThen(f: (L) -> Either<T, @UnsafeVariance R>): Either<T, R> {
        return when (this) {
            is Left -> f(this.data)
            is Right -> this
        }
    }
}

typealias Result<L> = Either<L, String>
