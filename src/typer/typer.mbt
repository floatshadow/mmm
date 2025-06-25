///|
typealias @abstract.Expr

///|
typealias @abstract.Type

///|
typealias @syntax.Bounding

///|
typealias @syntax.DBlvl

///|
pub struct TyCtx {
  values : VEnv
  typs : VEnv
  sig : Sig
  lvl : DBlvl
  bounds : List[Bounding]
}

///|
pub fn TyCtx::new() -> TyCtx {
  TyCtx::{ values: Nil, typs: Nil, sig: Sig::new(), lvl: 0, bounds: Nil }
}

// Free variables comes from binding forms such as λx. t.
// These free variables in Γ are neutral values 
// since we don't know their values.

///|
pub fn TyCtx::add_binding_var(
  self : TyCtx,
  name : String,
  typ : TypeVal
) -> TyCtx {
  let value = VNe(Neutral::var(name))
  {
    ..self,
    values: self.values.add((name, value)),
    typs: self.typs.add((name, typ)),
    lvl: DBlvl(self.lvl.inner() + 1),
    bounds: self.bounds.add(Bounding::Bound),
  }
}

// Free variables comes from definitions such as let
// In let binding, we would obtain the value of
// variable in Γ, so we can use it as a value.

///|
pub fn TyCtx::add_definition_var(
  self : TyCtx,
  name : String,
  value : Value,
  typ : TypeVal
) -> TyCtx {
  {
    ..self,
    values: self.values.add((name, value)),
    typs: self.typs.add((name, typ)),
    lvl: DBlvl(self.lvl.inner() + 1),
    bounds: self.bounds.add(Bounding::Defined),
  }
}

///|
pub fn TyCtx::lvl(self : TyCtx) -> Int {
  self.lvl.inner()
}

///|
pub fn TyCtx::boundings(self : TyCtx) -> List[Bounding] {
  self.bounds
}

// Bidirectional type checking:
// We follow Agda [Norell's thesis], where type checker produce
// a well typed term from input expression rather than just check
// that is well typed.
// General paradigms to decide when to infernece or checking is that 
// given the principal type connectives:
//   - introduction forms: checking
//   - elimination forms: inference
//
// Two rules dicates the mode change between checking and inference
// Γ  ⊢ e ⇐ A
// --------------- (T-Anno)
// Γ |- e : A ⇒ A 
// 
// Γ  ⊢ e ⇒ A   Γ |- A ≡ B
// ------------------------ (T-Conv)
// Γ  ⊢ e ⇐ B
//
// The implicit argument insertion is based on section 2.6 of 
// Elaboration with first-class implicit function types.

///| Insert fresh implicit applications to an expr
/// which is not a implicit lambda.
///   insert λ{x}. t  _                ->  λ{x}. t
///   insert t        Π {x : A}. B[x]  ->  t {u}
fn insert_implicit_app(
  ctx : TyCtx,
  hiding_lam : (Expr, TypeVal)
) -> (Expr, TypeVal) raise Failure {
  fn go(t : Expr, a : TypeVal) -> (Expr, TypeVal) raise Failure {
    match a {
      VPi(_, Hiding, _, b) => {
        let m = fresh_meta(ctx)
        let mv = eval(ctx.values, ctx.sig, m)
        go(App(t, m, Hiding), b(mv))
      }
      _ => (t, a)
    }
  }

  match hiding_lam {
    (Lam(UntypedBinding((_, Hiding)), _) as t, ty) => (t, ty)
    (t, a) => go(t, a)
  }
}

///|
pub struct Typer {
  tracer : @util.SubTracer
}

///|
pub fn Typer::new(tracer : @util.SubTracer) -> Typer {
  Typer::{ tracer, }
}

///|
fn Typer::check_expr_is_type(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr
) -> (Expr, Int) raise Failure {
  match self.infer(ctx, expr) {
    (t, VSet(i)) => (t, i)
    _ => fail("\{expr.to_pretty()} is not a type")
  }
}

///|
pub fn Typer::check(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr,
  typ : TypeVal
) -> Expr raise Failure {
  self.tracer.log("check \{expr.to_pretty()} <= \{typ}")
  match (expr, typ) {
    // If the Hiding info of the lambda matches the Pi type
    // Γ, x : A  ⊢ t : B[x] ⇝ t'
    // ------------------------------------------
    // Γ  ⊢  λx. t ⇐ (x : A) -> B[x] ⇝ λx. t'
    (Lam(UntypedBinding((_, x, h1)), t), VPi(_, h2, a, b)) if h1 == h2 => {
      let x = x.to_raw_name()
      let ctx2 = ctx.add_binding_var(x, a)
      let t = self.check(ctx2, t, b(VNe(Neutral::vvar(ctx.lvl()))))
      Lam(UntypedBinding((x, h1)), t)
    }
    // Otherwise if Pi is hiding, insert a new implicit lambda
    // Γ, x : A  ⊢ t : B[x] ⇝ t'
    // ------------------------------------------
    // Γ  ⊢ t ⇐ {x : A} -> B[x] ⇝ λx. t'
    (t, VPi(x, Hiding, a, b)) => {
      let ctx2 = ctx.add_binding_var(x, a)
      let t = self.check(ctx2, t, b(VNe(Neutral::vvar(ctx.lvl()))))
      Lam(UntypedBinding((x, Hiding)), t)
    }
    (Hole(_), a) => {
      fresh_meta(ctx)
    }
    // Γ  ⊢ e ⇒ B   A ≡ B (NbE & unify)
    // -------------------
    // Γ  ⊢ e ⇐ A
    (t, expected_tyval) => {
      let (t, infer_tyval) = self.infer(ctx, t)
      // check if inferred type is equal to given type
      self.unify_err(ctx.values, ctx.sig,  ctx.lvl(), infer_tyval, expected_tyval)
      t
    }
  }
}

///|
fn Typer::infer_app(
  self : Typer,
  ctx : TyCtx,
  t : @concrete.Expr,
  u : @concrete.Expr
) -> (Expr, TypeVal) raise Failure {
  let (f, f_tyval) = self.infer(ctx, f)
  match f_tyval {
    VPi(_, _, param_ty_value, return_ty_func) => {
      // check the argument type
      self.check(ctx, arg, param_ty_value)
      // return the function type applied to the argument
      (App(f, arg, h), return_ty_func(eval(ctx.values, ctx.sig, arg)))
    }
    _ => fail("\{f} is not of (dependent) function type")
  }
}

///|
pub fn Typer::infer(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr
) -> (Expr, TypeVal) raise Failure {
  self.tracer.log("infer \{expr.to_pretty()}")
  let (expr, tyval) = match expr {
    // (x : A) ∈ Γ
    // ------------
    // Γ |- x  ⇒ A
    Ident(x) => {
      let x = x.to_raw_name()
      // de burijn index
      fn go(index : Int, types : VEnv) -> (Int, TypeVal)? {
        match types {
          Cons((y, v), tl) =>
            if x == y {
              Some((index, v))
            } else {
              go(index + 1, tl)
            }
          Nil => None
        }
      }

      match go(0, ctx.typs) {
        Some(it) => it
        None =>
          match ctx.sig.constants.get(x) {
            Some(f) => (Def(x), f.ty)
            None =>
              match ctx.sig.cons.get(x) {
                Some(c) => (Con(x), c.ty)
                None => fail("does not find \{x} in env when evaluation!")
              }
          }
      }
    }
    // -------------------------
    // Γ |- Set i => Set (i + 1)
    Set(_, i) => (Set(i), VSet(i + 1))
    // Γ |- e1 => A -> B  Γ, x : A |- e2 <= A
    // ---------------------------------------
    // Γ |- e1 e2 => B[x |-> t]
    // App(f, arg) => {
    //   let infer_f_ty = infer(ctx, f)
    //   match infer_f_ty {
    //     VPi(param_ty_value, return_ty_func) => {
    //       check(ctx, arg, param_ty_value)
    //       return_ty_func(eval(ctx.values, arg))
    //     }
    //     _ => fail("\{f} is not of (dependent) function type")
    //   }
    // }
    HiddenArg(_) => fail("hidden argument should not be inferred individually!")
    Lam(UntypedBinding((_, x, h)), t) => {
      // \ x : ?m .t
      let a = eval(ctx.values, ctx.sig, fresh_meta(ctx))
      let x = x.to_raw_name()
      let ctx2 = ctx.add_binding_var(x, a)
      let (t, b) = self.infer(ctx2, t)
      let (t, b) = insert_implicit_app(ctx2, (t, b))
      fn b_tyval(a : TypeVal) -> TypeVal raise Failure {
        let env2 = ctx.values.add((x, a))
        let b = readback_type(env2, ctx.sig, b)
        eval(ctx.values.add((x, a)), ctx.sig, b)
      }

      (Lam(UntypedBinding((x, h)), t), VPi(x, h, a, b_tyval))
    }
    // Γ |- A => Set i  Γ, x : A |- B[x] => Set j
    // -----------------------------------------
    // Γ |- Π (x : A). B[x] => Set (max(i, j))
    Pi(TypedBinding((_, x, h, a)), b) => {
      let x = x.to_raw_name()
      let (a, a_univ) = self.check_expr_is_type(ctx, a)
      let a_tyval = eval(ctx.values, ctx.sig, a)
      let ctx2 = ctx.add_binding_var(x, a_tyval)
      let (b, b_univ) = self.check_expr_is_type(ctx2, b)
      (Pi(TypedBinding((x, h, a)), b), VSet(@math.maximum(a_univ, b_univ)))
    }
    Hole(_) => {
      let a = eval(ctx.values, ctx.sig, fresh_meta(ctx))
      let t = fresh_meta(ctx)
      (t, a)
    }
    Dot(_) => fail("dot expression should not be used in expression!")
    // Γ |- e1 <= A  Γ, x : A |- e2 => B
    // ----------------------------------
    // Γ |- let x : A = e1 in e2 => B
    // Let((x, x_typ), e1, e2) => {
    //   let _ = check_expr_is_type(ctx, x_typ)
    //   let x_typ_value = eval(ctx.values, x_typ)
    //   // println("let \{x}: \{x_typ_value}")
    //   let _ = check(ctx, e1, x_typ_value)
    //   let e1_value = eval(ctx.values, e1)
    //   // println("let \{x} = \{e1_value}")
    //   let ctx2 = ctx.add_definition_var(x, e1_value, x_typ_value)
    //   infer(ctx2, e2)
    // }
  }
  self.tracer.log("infer \{expr.to_pretty()} => \{tyval}")
  (expr, tyval)
}

///|
fn TyCtx::add_axiom(self : TyCtx, name : String, ty : TypeVal) -> TyCtx {
  let axiom = ConstantDef::{ name, ty, definitions: None }
  {
    ..self,
    sig: { ..self.sig, constants: self.sig.constants.add(name, axiom) },
  }
}

///|
fn Typer::axiom_check(
  self : Typer,
  ctx : TyCtx,
  name : Name,
  ty : @concrete.Expr
) -> TyCtx raise Failure {
  let name = name.to_raw_name()
  let (ty, _) = self.check_expr_is_type(ctx, ty)
  let tyval = eval(ctx.values, ctx.sig, ty)
  ctx.add_axiom(name, tyval)
}

///|
fn Typer::data_check(
  self : Typer,
  ctx : TyCtx,
  name : Name,
  param : @concrete.Telescope,
  ty : @concrete.Expr,
  cons : Array[@concrete.Declaration]
) -> TyCtx raise Failure {
  // data
  let data_ty = @concrete.Expr::telescope_pi(param, ty)
  // constructors
  for con in cons {
    match con {
      TypeSig(x, ty) => {
        let (ty, _) = self.check_expr_is_type(ctx, ty)
        let tyval = eval(ctx.values, ctx.sig, ty)
        ctx = ctx.add_axiom(x.to_raw_name(), tyval)
      }
      _ => fail("constructor declaration not implemented yet")
    }
  }
  fail("data check not implemented yet")
}

///|
fn Typer::check_declarations(
  self : Typer,
  ctx : TyCtx,
  decls : Array[@concrete.Declaration]
) -> Unit raise Failure {
  let checked_decls = []
  let mut ctx2 = ctx
  for decl in decls {
    self.tracer.log("check declaration")
    self.tracer.log(decl.to_pretty())
    let checked_decl = match decl {
      TypeSig(x, ty) => ctx2 = self.axiom_check(ctx2, x, ty)
      DataDef(_, d, telescope, ty, cons) =>
        ctx2 = self.data_check(ctx2, d, telescope, ty, cons)
      FunClause(_) => ...
      Mutual(_) | Postulate(_) | Command(_) => fail("not implemented yet")
    }
    checked_decls.push(checked_decl)
  }
}

///|
pub fn Typer::check_program(
  self : Typer,
  program : Array[@concrete.Declaration]
) -> Unit raise Failure {
  let ctx = TyCtx::new()
  self.check_declarations(ctx, program)
}

///|
pub fn alpha_equiv(e1 : Expr, e2 : Expr) -> Bool {
  match (e1, e2) {
    (Var(i1), Var(i2)) => i1 == i2
    (Set(u1), Set(u2)) => u1 == u2
    (Pi(TypedBinding((_, h1, a1)), b1), Pi(TypedBinding((_, h2, a2)), b2)) if h1 ==
      h2 => alpha_equiv(a1, a2) && alpha_equiv(b1, b2)
    (Lam(UntypedBinding((_, h1)), t1), Lam(UntypedBinding((_, h2)), t2)) if h1 ==
      h2 => alpha_equiv(t1, t2)
    (App(f1, a1, h1), App(f2, a2, h2)) if h1 == h2 =>
      alpha_equiv(f1, f2) && alpha_equiv(a1, a2)
    _ => false
  }
}

///|
pub struct PrettyTyCtx {
  ctx : TyCtx
}
