/**
 * data Value
 * = VLam (Value → Value)
 * | VStar
 * | VPi Value (Value → Value)
 * | VNeutral Neutral
 * | VNat
 * | VZero
 * | VSucc Value
 * | VNil Value
 * | VCons Value Value Value Value
 * | VVec Value Value
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