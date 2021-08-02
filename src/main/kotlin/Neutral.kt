/**
 * data Neutral
 * = NFree Name
 * | NApp Neutral Value
 * | NNatElim Value Value Value Neutral
 * | NVecElim Value Value Value Value Value Neutral
 */
sealed class Neutral {
    data class NFree(val name: Name) : Neutral()
    data class NApp(val neutral: Neutral, val value: Value) : Neutral()
    data class NNatElem(val a: Value, val b: Value, val c: Value, val d: Neutral) : Neutral()
    data class NVecElem(val a: Value, val b: Value, val c: Value, val d: Value, val e: Value, val f: Neutral) :
        Neutral()
}