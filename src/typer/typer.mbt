///|
typealias @abstract.Expr

///|
typealias @abstract.Type

///|
typealias @syntax.Bounding

///|
typealias @syntax.DBlvl

///|
typealias @util.Range

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
  let value = VNe(Neutral::vvar(self.lvl()))
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

pub fn TyCtx::pp_gamma(self : TyCtx) -> String raise Failure {
  let buffer = @buffer.new()
  for lvl, binds in self.typs.rev().iter2() {
    let (name, ty) = binds
    buffer.write_string("\{name} : \{readback(lvl, ty).to_pretty()}, ")
  }
  buffer.to_string()
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
  self.tracer.log("check \{expr.to_pretty()} ⇐ \{readback(ctx.lvl(), typ).to_pretty()}")
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
    (Hole(_), a) => fresh_meta(ctx)
    // Γ  ⊢ e ⇒ B   A ≡ B (NbE & unify)
    // -------------------
    // Γ  ⊢ e ⇐ A
    (t, expected_tyval) => {
      let (t, infer_tyval) = self.infer(ctx, t)
      // check if inferred type is equal to given type
      self.unify_err(
        ctx.values,
        ctx.sig,
        ctx.lvl(),
        infer_tyval,
        expected_tyval,
      )
      t
    }
  }
}

///|
pub fn Typer::infer(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr
) -> (Expr, TypeVal) raise Failure {
  let gamma = ctx.pp_gamma()
  self.tracer.log("infer \{gamma} ⊢ \{expr.to_pretty()}")
  let (expr, ty) : (Expr, TypeVal) = match expr {
    // (x : A) ∈ Γ
    // ------------
    // Γ ⊢ x  ⇒ A ⇝ x
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
        Some((idx, ty)) => (Var(idx), ty)
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
    // Γ ⊢ Set (i) ⇒ Set (i + 1) ⇝ Set (i)
    Set(_, i) => (Set(i), VSet(i + 1))
    // Γ ⊢ e1 ⇒ A -> B ⇝ t   Γ, x : A ⊢ e2 ⇐ A  ⇝ u
    // -----------------------------------------
    // Γ ⊢ e1 e2 ⇒ B[t] ⇝ t u
    RawApp(_, es) => {
      let apps = match es {
        Cons(e1, e2, es2) =>
          loop (e1, e2, es2) {
            (e1, e2, Nil) =>
              break @concrete.App(Range::merge_range(e1, e1), e1, e2)
            (e1, e2, Cons(e3, es3)) =>
              continue (
                  @concrete.App(Range::merge_range(e1, e1), e1, e2),
                  e3,
                  es3,
                )
          }
      }
      self.infer(ctx, apps)
    }
    App(_, t, u) => {
      let (t, t_tyval, h) : (Expr, TypeVal, Hiding) = match u {
        HiddenArg(_) => {
          let (t, t_tyval) = self.infer(ctx, t)
          (t, t_tyval, Hiding)
        }
        _ => {
          let (t, t_tyval) = insert_implicit_app(ctx, self.infer(ctx, t))
          (t, t_tyval, NotHiding)
        }
      }
      // ensure t is of Pi type
      let (a, b) = match force_meta(ctx.values, ctx.sig, t_tyval) {
        VPi(_, h2, a, b) => {
          guard h == h2 else { fail("hiding mismatch: \{h} != \{h2}") }
          (a, b)
        }
        _ => {
          let a = eval(ctx.values, ctx.sig, fresh_meta(ctx))
          fn b_tyval(a : TypeVal) -> TypeVal raise Failure {
            let ctx2 = ctx.add_binding_var("x", a)
            let b = fresh_meta(ctx2)
            eval(ctx.values, ctx.sig, b)
          }

          self.unify_err(
            ctx.values,
            ctx.sig,
            ctx.lvl(),
            t_tyval,
            VPi("x", h, a, b_tyval),
          )
          (a, b_tyval)
        }
      }
      let u = self.check(ctx, u, a)
      (App(t, u, h), b(eval(ctx.values, ctx.sig, u)))
    }
    HiddenArg(_) => fail("hidden argument should not be inferred individually!")
    Lam(UntypedBinding((_, x, h)), t) => {
      // \ x : ?m .t
      let a = eval(ctx.values, ctx.sig, fresh_meta(ctx))
      let x = x.to_raw_name()
      let ctx2 = ctx.add_binding_var(x, a)
      let (t, b) = insert_implicit_app(ctx2, self.infer(ctx2, t))
      fn b_tyval(a : TypeVal) -> TypeVal raise Failure {
        let b = readback(ctx.lvl() + 1, b)
        eval(ctx.values.add((x, a)), ctx.sig, b)
      }

      (Lam(UntypedBinding((x, h)), t), VPi(x, h, a, b_tyval))
    }
    // Γ ⊢ A ⇒ Set (i)  Γ, x : A ⊢ B[x] ⇒ Set j
    // -----------------------------------------
    // Γ ⊢ Π (x : A). B[x] ⇒ Set (max(i, j))
    Pi(TypedBinding((_, x, h, a)), b) => {
      let x = x.to_raw_name()
      let (a, a_univ) = self.check_expr_is_type(ctx, a)
      let a_val = eval(ctx.values, ctx.sig, a)
      let ctx2 = ctx.add_binding_var(x, a_val)
      let (b, b_univ) = self.check_expr_is_type(ctx2, b)
      (Pi(TypedBinding((x, h, a)), b), VSet(@math.maximum(a_univ, b_univ)))
    }
    Hole(_) => {
      let a = eval(ctx.values, ctx.sig, fresh_meta(ctx))
      let t = fresh_meta(ctx)
      (t, a)
    }
    Dot(_) => fail("dot expression should not be used in expression!")
  }
  // self.tracer.log("infer \{expr.to_pretty()} ⇒ \{ty}")
  self.tracer.log("infer \{gamma} ⊢ \{expr.to_pretty()} ⇒ \{readback(ctx.lvl(), ty).to_pretty()}")
  (expr, ty)
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
  self.tracer.log("axiom \{name} : \{tyval}")
  ctx.add_axiom(name, tyval)
}

///|
// fn Typer::data_check(
//   self : Typer,
//   ctx : TyCtx,
//   name : Name,
//   param : @concrete.Telescope,
//   ty : @concrete.Expr,
//   cons : Array[@concrete.Declaration]
// ) -> TyCtx raise Failure {
//   // data
//   let data_ty = @concrete.Expr::telescope_pi(param, ty)
//   // constructors
//   for con in cons {
//     match con {
//       TypeSig(x, ty) => {
//         let (ty, _) = self.check_expr_is_type(ctx, ty)
//         let tyval = eval(ctx.values, ctx.sig, ty)
//         ctx = ctx.add_axiom(x.to_raw_name(), tyval)
//       }
//       _ => fail("constructor declaration not implemented yet")
//     }
//   }
//   fail("data check not implemented yet")
// }

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
      // TypeSig(x, ty) => ctx2 = self.axiom_check(ctx2, x, ty)
      DataDef(_, d, telescope, ty, cons) =>
        fail("data definition not implemented yet")
      Postulate(r, ds) =>
        for d in ds {
          match d {
            TypeSig(x, ty) => {
              self.tracer.log("check declaration in postulate")
              self.tracer.log(d.to_pretty())
              ctx2 = self.axiom_check(ctx2, x, ty)
            }
            _ =>
              fail(
                "postulate at \{r} constains non-axiom declaration \{d.to_pretty()}",
              )
          }
        }
      TypeSig(_) | Mutual(_) | FunClause(_) | Command(_) =>
        fail("not implemented yet")
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
  let unsolved_metas = unsolved_metas()
  if unsolved_metas.is_empty() {
    println("All Done.")
  } else {
    println("Unsolved metas:")
    for meta_info in unsolved_metas {
      let (mv, ty) = meta_info
      println("\{mv} : \{ty}")
    }
  }
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
