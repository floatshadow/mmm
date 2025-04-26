///|
typealias Syntax = @types.Syntax

///|
typealias Type = @types.Type

///|
fn pi(param : (String, Syntax), return_ty : Syntax) -> Syntax {
  Pi(param.0, param.1, return_ty)
}

///|
fn lam(param : String, body : Syntax) -> Syntax {
  Lam(param, body)
}

///|
fn app(f : String, args : Array[Syntax]) -> Syntax {
  args.iter().fold(init=Var(f), fn(f, a) { App(f, a) })
}

///|
fn appE(f : Syntax, args : Array[Syntax]) -> Syntax {
  args.iter().fold(init=f, fn(f, a) { App(f, a) })
}

///|
let predef : Array[(String, Type)] = [
  ("Nat", Set(0)),
  ("zero", Var("Nat")),
  ("succ", pi(("n", Var("Nat")), Var("Nat"))),
  ("Bool", Set(0)),
  ("tt", Var("Bool")),
  ("ff", Var("Bool")),
  (
    "if",
    pi(
      ("A", Set(0)),
      pi(
        ("cond", Var("Bool")),
        pi(("condseq", Var("A")), pi(("alter", Var("A")), Var("A"))),
      ),
    ),
  ),
  ("List", pi(("A", Set(0)), pi(("n", Var("Nat")), Set(0)))),
  ("nil", pi(("A", Set(0)), app("List", [Var("A"), Var("zero")]))),
  (
    "cons",
    pi(
      ("A", Set(0)),
      pi(
        ("n", Var("Nat")),
        pi(
          ("hd", Var("A")),
          pi(
            ("tl", app("List", [Var("A"), Var("n")])),
            app("List", [Var("A"), app("succ", [Var("n")])]),
          ),
        ),
      ),
    ),
  ),
  (
    "eq",
    pi(("A", Set(0)), pi(("lhs", Var("A")), pi(("rhs", Var("A")), Set(0)))),
  ),
  (
    "refl",
    pi(
      ("A", Set(0)),
      pi(("a", Var("A")), app("eq", [Var("A"), Var("a"), Var("a")])),
    ),
  ),
]

///|
fn check_expr_has_type(typ : Type, expr : Syntax) -> Syntax {
  Let(("checked", typ), expr, Var("checked"))
}

///|
fn test_infer_nbe(expr : Syntax) -> Syntax!Failure {
  let mut env = TyCtx::empty()
  for ntyp in predef {
    let (name, typ) = ntyp
    env = env.add_neutral_var(name, eval!(env.values, typ))
  }
  readback!(infer!(env, expr), env.names)
}

///|
test "boolean and" {
  // λ x. λ y. if x y ff
  let ex1 = lam(
    "x",
    lam("y", app("if", [Var("Bool"), Var("x"), Var("y"), Var("ff")])),
  )
  let typ = pi(("x", Var("Bool")), pi(("y", Var("Bool")), Var("Bool")))
  // infer with type annotation
  let elab = test_infer_nbe!(Let(("band", typ), ex1, Var("band")))
  assert_true!(alpha_equiv(@immut/hashmap.new(), elab, typ))
}

///|
test "function application" {
  // {A : Set} {B : Π (x : A). Set} λ (f : Π (x : A). B(x)). λ (a : A). f a
  let ex2 = lam("A", lam("B", lam("f", lam("a", app("f", [Var("a")])))))
  let typ = pi(
    ("A", Set(0)),
    pi(
      ("B", pi(("x", Var("A")), Set(0))),
      pi(
        ("f", pi(("x", Var("A")), app("B", [Var("x")]))),
        pi(("a", Var("A")), app("B", [Var("a")])),
      ),
    ),
  )
  // infer with type annotation
  let elab = test_infer_nbe!(Let(("compose", typ), ex2, Var("compose")))
  assert_true!(alpha_equiv(@immut/hashmap.new(), elab, typ))
}

///|
test "expression equality" {
  // λ (x : Nat). x
  let id = lam("x", Var("x"))
  let idnat_typ = pi(("x", Var("Nat")), Var("Nat"))
  let idnat : Syntax = Let(("idNat", idnat_typ), id, Var("idNat"))

  // refl n : (id n = n)
  let ex3 = lam(
    "n",
    check_expr_has_type(
      app("eq", [Var("Nat"), appE(idnat, [Var("n")]), Var("n")]),
      app("refl", [Var("Nat"), Var("n")]),
    ),
  )
  let typ = pi(("n", Var("Nat")), app("eq", [Var("Nat"), Var("n"), Var("n")]))
  let elab = test_infer_nbe!(Let(("refln", typ), ex3, Var("refln")))
  assert_true!(alpha_equiv(@immut/hashmap.new(), elab, typ))
}

///|
test "function equality" {

  // {A : Set} Π (a : A). A
  let eqA = pi(("a", Var("A")), Var("A"))
  // {A : Set} |- λ (x : A). x : Π (a : A). A
  let idA = lam("x", Var("x"))
  let idA_checked : Syntax = Let(("idA", eqA), idA, Var("idA"))

  // {A : Set} {B : Π (x : A). Set} λ (f : Π (x : A). B(x)). λ (a : A). f a
  let ex2 = lam("A", lam("B", lam("f", lam("a", app("f", [Var("a")])))))
  let ex2_typ = pi(
    ("A", Set(0)),
    pi(
      ("B", pi(("x", Var("A")), Set(0))),
      pi(
        ("f", pi(("x", Var("A")), app("B", [Var("x")]))),
        pi(("a", Var("A")), app("B", [Var("a")])),
      ),
    ),
  )
  let ex2_checked : Syntax = Let(("ex2", ex2_typ), ex2, Var("ex2"))
  let ex4 : Syntax = lam(
    "A",
    check_expr_has_type(
      // {A : Set} |- refl {Π (a : A). A} idA : λ (x : A). x = (λ (a : A). A) (λ (x : A). x)
      app("eq", [
        eqA,
        idA_checked,
        appE(ex2_checked, [Var("A"), lam("a", Var("A")), idA_checked]),
      ]),
      app("refl", [eqA, idA_checked]),
    ),
  )
  let typ = pi(("A", Set(0)), app("eq", [eqA, idA, lam("a", Var("a"))]))
  let elab = test_infer_nbe!(Let(("reflidA", typ), ex4, Var("reflidA")))
  assert_true!(alpha_equiv(@immut/hashmap.new(), elab, typ))
}
