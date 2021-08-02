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
 * type↑ i 0Nat =return VStar
 * type↑ i 0Zero =return VNat
 * type↑ i 0(Succ k)=
 *      do type↓ i 0k VNat
 *      return VNat
 * type↑ i 0(NatElim m mz ms k)=
 *      do
 *          type↓ i 0m (VPi VNat (const VStar))
 *          let mVal =eval↓ m [ ]
 *          type↓ i 0mz (mVal ‘vapp‘ VZero)
 *          type↓ i 0ms (VPi VNat (λl →VPi (mVal ‘vapp‘ l)(λ→mVal ‘vapp‘ VSucc l)))
 *          type↓ i 0k VNat
 *          let kVal =eval↓ k [ ]
 *          return (mVal ‘vapp‘ kVal)
 * type↑ i 0(Vec αk)=
 *      do
 *          type↓ i 0αVStar
 *          type↓ i 0k VNat
 *          return VStar
 * type↑ i 0(Nil α)=
 *      do
 *          type↓ i 0αVStar
 *          let aVal =eval↓ α[ ]
 *          return (VVec aVal VZero)
 * type↑ i 0 (Cons αk x xs)=
 *      do
 *          type↓ i 0αVStar
 *          let aVal =eval↓ α[ ]
 *          type↓ i 0k VNat
 *          let kVal =eval↓ k [ ]
 *          type↓ i 0x aVal
 *          type↓ i 0xs (VVec aVal kVal)
 *          return (VVec aVal (VSucc kVal))
 * type↑ i 0(VecElim αm mn mc k vs)=
 *      do type↓ i 0αVStar
 *          let aVal =eval↓ α[ ]
 *          type↓ i 0m (VPi VNat (λk →VPi (VVec aVal k)(λ→VStar)))
 *          let mVal =eval↓ m [ ]
 *          type↓ i 0mn (foldl vapp mVal [VZero,VNil aVal])
 *          type↓ i 0mc (VPi VNat (λl →
 *              VPi aVal (λy →
 *              VPi (VVec aVal l)(λys →
 *              VPi (foldl vapp mVal [l,ys])(λ→
 *              (foldl vapp mVal [VSucc l,VCons aVal l y ys]))))))
 *          type↓ i 0k VNat
 *          let kVal =eval↓ k [ ]
 *          type↓ i 0vs (VVec aVal kVal)
 *          let vsVal =eval↓ vs [ ]
 *          return (foldl vapp mVal [kVal,vsVal])
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
            typeDownArrow(i, context, m, Value.VPi(Value.VNat) { Value.VStar }).andThen {
                val mVal = evalCheckableTerm(m, emptyList())
                typeDownArrow(i, context, mz, vApp(mVal, Value.VZero)).andThen {
                    typeDownArrow(i, context, ms, Value.VPi(Value.VNat) { l ->
                        Value.VPi(vApp(mVal, l)) {
                            vApp(mVal, Value.VSucc(l))
                        }
                    }).andThen {
                        typeDownArrow(i, context, k, Value.VNat).andThen {
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
        is InferableTerm.Cons -> typeDownArrow(i, context, infTerm.a, Value.VStar).andThen {
            val aVal = evalCheckableTerm(infTerm.a, emptyList())
            typeDownArrow(i, context, infTerm.b, Value.VNat).andThen {
                val kVal = evalCheckableTerm(infTerm.b, emptyList())
                typeDownArrow(i, context, infTerm.c, aVal).andThen {
                    typeDownArrow(i, context, infTerm.d, Value.VVec(aVal, Value.VSucc(kVal))).andThen {
                        Either.Left(Value.VVec(aVal, (Value.VSucc(kVal))))
                    }
                }
            }
        }
        is InferableTerm.Nil -> typeDownArrow(i, context, infTerm.type, Value.VStar).andThen {
            val aVal = evalCheckableTerm(infTerm.type, emptyList())
            Either.Left(Value.VVec(aVal, Value.VZero))
        }
        is InferableTerm.Vec -> typeDownArrow(i, context, infTerm.a, Value.VStar).andThen {
            typeDownArrow(i, context, infTerm.b, Value.VNat).andThen {
                Either.Left(Value.VStar)
            }
        }
        is InferableTerm.VecElim -> typeDownArrow(i, context, infTerm.a, Value.VStar).andThen {
            val aVal = evalCheckableTerm(infTerm.a, emptyList())
            typeDownArrow(
                i,
                context,
                infTerm.b,
                Value.VPi(Value.VNat) { k -> Value.VPi(Value.VVec(aVal, k)) { Value.VStar } })
                .andThen {
                    val mVal = evalCheckableTerm(infTerm.b, emptyList())
                    typeDownArrow(
                        i,
                        context,
                        infTerm.c,
                        listOf(Value.VZero, Value.VNil(aVal)).fold(mVal) { a, b -> vApp(a, b) }).andThen {
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
                        }).andThen {
                            typeDownArrow(i, context, infTerm.e, Value.VNat).andThen {
                                val kVal = evalCheckableTerm(infTerm.e, emptyList())
                                typeDownArrow(i, context, infTerm.f, Value.VVec(aVal, kVal)).andThen {
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
 * type↓ :: Int → Context → Term↓ → Type → Result ()
 * type↓ i 0 (Inf e) τ = do
 *      τ′ ←type↑ i 0e
 *      unless (τ == τ′) (throwError "type mismatch")
 * type↓ i 0 (Lam e) (Fun τ τ′) = type↓ (i + 1) ((Local i, HasType τ) : 0) (subst↓ 0 (Free (Local i)) e) τ′
 * type↓ i 0 _ _ = throwError "type mismatch"
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
        is InferableTerm.TStar -> InferableTerm.TStar
        else -> throw RuntimeException("internal Error")
    }
}

/**
 * subst↓ :: Int → Term↑ → Term↓ → Term↓
 * subst↓ i r (Inf e) = Inf (subst↑ i r e)
 * subst↓ i r (Lam e) = Lam (subst↓ (i +1) r e)
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
        is Value.VStar -> CheckableTerm.Inf(InferableTerm.TStar)
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