import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

/**
 * id′ =Lam (Inf (Bound 0))
 * const′ =Lam (Lam (Inf (Bound 1)))
 * tfree α=TFree (Global α)
 * free x =Inf (Free (Global x))
 * term1 =Ann id′ (Fun (tfree "a")(tfree "a")):@: free "y"
 * term2 =Ann const′ (Fun (Fun (tfree "b")(tfree "b")) (Fun (tfree "a") (Fun (tfree "b")(tfree "b")))) :@: id′ :@: free "y"
 * env1 =[(Global "y",HasType (tfree "a")),
 * (Global "a",HasKind Star)]
 * env2 =[(Global "b",HasKind Star)] ++env1
 */

class Tester {
    @Test
    // id′ =Lam (Inf (Bound 0))
    internal fun `create id`() {
        CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0)))
    }

    @Test
    // const′ =Lam (Lam (Inf (Bound 1)))
    internal fun create_const() {
        CheckableTerm.Lam(CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(1))))
    }

    @Test
    // term1 =Ann id′ (Fun (tfree "a")(tfree "a")):@: free "y"
    internal fun `create term1`() {
        val id = CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0)))
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        val free = fun(x: String) = CheckableTerm.Inf(InferableTerm.Free(Name.Global(x)))
        val term1 = InferableTerm.App(InferableTerm.Ann(id, Type.Fun(tfree("a"), tfree("a"))), free("y"))
        assertEquals(
            quoteZero(evalInferableTerm(term1, emptyList())),
            CheckableTerm.Inf(InferableTerm.Free(Name.Global("y")))
        )
    }

    @Test
    // term2 =Ann const′ (Fun (Fun (tfree "b")(tfree "b"))
    // (Fun (tfree "a")
    // (Fun (tfree "b")(tfree "b"))))
    // :@: id′ :@: free "y"
    internal fun `create term2`() {
        val id = CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0)))
        val const = CheckableTerm.Lam(CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(1))))
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        val free = fun(x: String) = CheckableTerm.Inf(InferableTerm.Free(Name.Global(x)))
        val term2 = InferableTerm.App(
            InferableTerm.App(
                InferableTerm.Ann(
                    const,
                    Type.Fun(Type.Fun(tfree("b"), tfree("b")), Type.Fun(tfree("a"), Type.Fun(tfree("b"), tfree("b"))))
                ), id
            ), free("y")
        )
        assertEquals(
            CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0))),
            quoteZero(evalInferableTerm(term2, emptyList()))
        )
    }

    @Test
    // env1 =[(Global "y",HasType (tfree "a")), (Global "a",HasKind Star)]
    internal fun `create env1`() {
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        listOf(Name.Global("y") to Info.HasType(tfree("a")), Name.Global("a") to Info.HasKind(Kind.Star))
    }

    @Test
    // env2 = [(Global "b",HasKind Star)] ++env
    internal fun `create env2`() {
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        val env1 = listOf(Name.Global("y") to Info.HasType(tfree("a")), Name.Global("a") to Info.HasKind(Kind.Star))
        listOf(Name.Global("b") to Info.HasKind(Kind.Star), *env1.toTypedArray())
    }

    @Test
    internal fun `typecheck env1 term1`() {
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        val id = CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0)))
        val free = fun(x: String) = CheckableTerm.Inf(InferableTerm.Free(Name.Global(x)))
        val env1 = listOf(Name.Global("y") to Info.HasType(tfree("a")), Name.Global("a") to Info.HasKind(Kind.Star))
        val term1 = InferableTerm.App(InferableTerm.Ann(id, Type.Fun(tfree("a"), tfree("a"))), free("y"))
        assertEquals(Either.Left(Type.TFree(Name.Global("a"))), typeUpArrowZero(env1, term1))
    }

    @Test
    internal fun `typecheck env2 term2`() {
        val tfree = fun(a: String) = Type.TFree(Name.Global(a))
        val env1 = listOf(Name.Global("y") to Info.HasType(tfree("a")), Name.Global("a") to Info.HasKind(Kind.Star))
        val env2 = listOf(Name.Global("b") to Info.HasKind(Kind.Star), *env1.toTypedArray())
        val id = CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(0)))
        val const = CheckableTerm.Lam(CheckableTerm.Lam(CheckableTerm.Inf(InferableTerm.Bound(1))))
        val free = fun(x: String) = CheckableTerm.Inf(InferableTerm.Free(Name.Global(x)))
        val term2 = InferableTerm.App(
            InferableTerm.App(
                InferableTerm.Ann(
                    const,
                    Type.Fun(Type.Fun(tfree("b"), tfree("b")), Type.Fun(tfree("a"), Type.Fun(tfree("b"), tfree("b"))))
                ), id
            ), free("y")
        )
        assertEquals<Result<Type>>(
            Either.Left(
                Type.Fun(
                    Type.TFree(Name.Global("b")),
                    Type.TFree(Name.Global("b"))
                )
            ),
            typeUpArrowZero(env2, term2)
        )
    }
}