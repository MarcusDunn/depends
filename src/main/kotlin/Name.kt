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