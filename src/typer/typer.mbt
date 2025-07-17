///|
typealias @abstract.Expr

///|
typealias @abstract.Type

///|
typealias @syntax.Bounding

///|
typealias @syntax.DBlvl

///|
typealias @syntax.NamedArg

///|
typealias @util.Range

///|
fn bind_name(x1 : String, x2 : String) -> String {
  x1 + "#" + x2
}

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
  ty~ : TypeVal
) -> TyCtx {
  let value = VNe(Neutral::vvar(self.lvl()))
  {
    ..self,
    values: self.values.add((name, value)),
    typs: self.typs.add((name, ty)),
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
  ty~ : TypeVal
) -> TyCtx {
  {
    ..self,
    values: self.values.add((name, value)),
    typs: self.typs.add((name, ty)),
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
fn Typer::insert_hiding_app(
  self : Typer,
  ctx : TyCtx,
  hiding_lam : (Expr, TypeVal)
) -> (Expr, TypeVal) raise Failure {
  match hiding_lam {
    (Lam(UntypedBinding((_, Hiding)), _) as t, ty) => (t, ty)
    (t, a) => self.insert_hiding_app_unchecked(ctx, (t, a))
  }
}

///|
fn Typer::insert_hiding_app_unchecked(
  self : Typer,
  ctx : TyCtx,
  hiding_lam : (Expr, TypeVal)
) -> (Expr, TypeVal) raise Failure {
  fn go(t : Expr, a_val : TypeVal) -> (Expr, TypeVal) raise Failure {
    match force_meta(ctx.values, ctx.sig, a_val) {
      VPi(_, Hiding, a, b) => {
        let m = self.fresh_meta(ctx, a)
        let mv = eval(ctx.values, ctx.sig, m)
        let b_val = b(mv)
        go(App(t, m, Hiding), b_val)
      }
      _ => (t, a_val)
    }
  }

  let (t, a) = hiding_lam
  go(t, a)
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
pub fn Typer::fresh_meta(
  self : Typer,
  tyctx : TyCtx,
  mty : TypeVal
) -> @abstract.Expr {
  let meta = next_meta.val
  next_meta.val += 1
  metas.set(meta, MetaEntry::Unsolved(mty~))
  let mv = @abstract.MetaVar(meta)
  let boundings = tyctx.boundings()
  self.tracer.log("  fresh metavariable \{mv} \{boundings} : \{mty}")
  @abstract.InsertedMeta(mv, boundings)
}

///|
fn TyCtx::pp_gamma(self : TyCtx) -> String raise Failure {
  let buffer = @buffer.new()
  let mut has_binds = false
  for lvl, binds in self.typs.rev().iter2() {
    let (name, ty) = binds
    if has_binds {
      buffer.write_string(", ")
    } else {
      has_binds = true
    }
    buffer.write_string(
      "\{name} : \{readback(self.values, self.sig, lvl, ty).to_pretty()}",
    )
  }
  if not(has_binds) {
    buffer.write_string("∅")
  }
  buffer.to_string()
}

///|
fn Typer::check_expr_is_type(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr
) -> (Expr, Int) raise Failure {
  // match self.infer(ctx, expr) {
  //   (t, VSet(i)) => (t, i)
  //   _ => fail("\{expr.to_pretty()} is not a type")
  // }
  let t = self.check(ctx, expr, VSet(0))
  (t, 0)
}

///|
pub fn Typer::check(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr,
  ty : TypeVal
) -> Expr raise Failure {
  let gamma = ctx.pp_gamma()
  let ty_expr = readback(ctx.values, ctx.sig, ctx.lvl(), ty)
  self.tracer.log(
    "check? \{gamma} ⊢ \{expr.to_pretty()} ⇐ \{ty_expr.to_pretty()}",
  )
  let expr : Expr = match (expr, ty) {
    // If the Hiding info of the lambda matches the Pi type
    // Γ, x : A  ⊢ t : B[x] ⇝ t'
    // ------------------------------------------
    // Γ  ⊢  λx. t ⇐ (x : A) -> B[x] ⇝ λx. t'
    (Lam(UntypedBinding((_, x, h1)), t), VPi(_, h2, a, b)) if h1 == h2 => {
      let x = x.to_raw_name()
      let ctx2 = ctx.add_binding_var(x, ty=a)
      let t = self.check(ctx2, t, b(VNe(Neutral::vvar(ctx.lvl()))))
      Lam(UntypedBinding((x, h1)), t)
    }
    // Otherwise if Pi is hiding, insert a new implicit lambda
    // Γ, x : A  ⊢ t : B[x] ⇝ t'
    // ------------------------------------------
    // Γ  ⊢ t ⇐ {x : A} -> B[x] ⇝ λx. t'
    (t, VPi(x, Hiding, a, b)) => {
      let ctx2 = ctx.add_binding_var(x, ty=a)
      let t = self.check(ctx2, t, b(VNe(Neutral::vvar(ctx.lvl()))))
      Lam(UntypedBinding((x, Hiding)), t)
    }
    // TODO: currently, our NbE and unification are untyped.
    (Hole(_), a) => self.fresh_meta(ctx, a)
    // Γ  ⊢ e ⇒ B   A ≡ B (NbE & unify)
    // -------------------
    // Γ  ⊢ e ⇐ A
    (t, expected_tyval) => {
      self.tracer.log("  check mode ↪ infer mode")
      let (t, infer_tyval) = self.insert_hiding_app(ctx, self.infer(ctx, t))
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
  let gamma = ctx.pp_gamma()
  let ty_expr = readback(ctx.values, ctx.sig, ctx.lvl(), ty)
  self.tracer.log(
    "check! \{gamma} ⊢ \{expr.to_pretty()} ⇐ \{ty_expr.to_pretty()}",
  )
  expr
}

///|
pub fn Typer::infer(
  self : Typer,
  ctx : TyCtx,
  expr : @concrete.Expr
) -> (Expr, TypeVal) raise Failure {
  let gamma = ctx.pp_gamma()
  self.tracer.log("infer? \{gamma} ⊢ \{expr.to_pretty()}")
  let (expr, ty) : (Expr, TypeVal) = match expr {
    // (x : A) ∈ Γ
    // ------------
    // Γ ⊢ x  ⇒ A ⇝ x
    Ident(x) => {
      let x_raw = x.to_raw_name()
      // de burijn index
      fn go(index : Int, types : VEnv) -> (Int, TypeVal)? {
        match types {
          Cons((y, v), tl) =>
            if x_raw == y {
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
          match ctx.sig.constants.get(x_raw) {
            Some(f) => (Def(x_raw), f.ty)
            None =>
              match ctx.sig.cons.get(x_raw) {
                Some(c) => (Con(x_raw), c.ty)
                None => {
                  let r = x.get_range()
                  fail("at \{r}, identifier \{x} not found in env!")
                }
              }
          }
      }
    }
    // -------------------------
    // Γ ⊢ Set (i) ⇒ Set (i + 1) ⇝ Set (i)
    // TODO : temporarily rollback to type in type
    Set(_, i) => (Set(i), VSet(i))
    // Γ ⊢ e1 ⇒ A -> B ⇝ t   Γ, x : A ⊢ e2 ⇐ A  ⇝ u
    // -----------------------------------------
    // Γ ⊢ e1 e2 ⇒ B[t] ⇝ t u
    RawApp(_, es) => {
      let apps = match es {
        Cons(e1, e2, es2) =>
          loop (e1, e2, es2) {
            (e1, HiddenArg(r, x, e2), Nil) =>
              break @concrete.App(NoRange, e1, NamedArg((r, x, Hiding, e2)))
            (e1, e2, Nil) =>
              break @concrete.App(
                NoRange,
                e1,
                NamedArg((NoRange, None, NotHiding, e2)),
              )
            (e1, HiddenArg(r, x, e2), Cons(e3, es3)) =>
              continue (
                  @concrete.App(NoRange, e1, NamedArg((r, x, Hiding, e2))),
                  e3,
                  es3,
                )
            (e1, e2, Cons(e3, es3)) =>
              continue (
                  @concrete.App(
                    NoRange,
                    e1,
                    NamedArg((NoRange, None, NotHiding, e2)),
                  ),
                  e3,
                  es3,
                )
          }
      }
      self.infer(ctx, apps)
    }
    App(_, t, u) => {
      let (t, t_tyval, u, h) : (Expr, TypeVal, @concrete.Expr, Hiding) = match
        u {
        NamedArg((_, None, Hiding, u)) => {
          let (t, t_tyval) = self.infer(ctx, t)
          (t, t_tyval, u, Hiding)
        }
        NamedArg((_, None, NotHiding, u)) => {
          let (t, t_tyval) = self.insert_hiding_app_unchecked(
            ctx,
            self.infer(ctx, t),
          )
          (t, t_tyval, u, NotHiding)
        }
        NamedArg((r, Some(x), _, _)) =>
          fail("at \{r}, do not named hidden argument \{x}")
      }

      // ensure t is of Pi type
      let (a, b) = match force_meta(ctx.values, ctx.sig, t_tyval) {
        VPi(_, h2, a, b) => {
          guard h == h2 else {
            fail("In \{expr.to_pretty()}, hiding mismatch: \{h} != \{h2}")
          }
          (a, b)
        }
        _ => {
          // TODO: In presence of a universe hierarchy, we should
          // insert a fresh level metavariable ?l with ?a : Set(?l) and ?l' with b[x] : Set(?l')
          let a = eval(ctx.values, ctx.sig, self.fresh_meta(ctx, VSet(0)))
          fn b_tyval(x_val : Value) -> TypeVal raise Failure {
            let ctx2 = ctx.add_definition_var("x", x_val, ty=a)
            let b = self.fresh_meta(ctx2, VSet(0))
            eval(ctx2.values, ctx2.sig, b)
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
    HiddenArg(r, _, _) =>
      fail("at \{r}, hidden argument should not be inferred individually!")
    Lam(UntypedBinding((_, x, h)), t) => {
      // \ x : ?a .t
      // TODO: In presence of a universe hierarchy, we should
      // insert a fresh level metavariable ?l with ?a : Set(?l)
      let a = eval(ctx.values, ctx.sig, self.fresh_meta(ctx, VSet(0)))
      let x = x.to_raw_name()
      let ctx2 = ctx.add_binding_var(x, ty=a)
      let (t, b) = self.insert_hiding_app(ctx2, self.infer(ctx2, t))
      fn b_tyval(x_val : Value) -> TypeVal raise Failure {
        let ctx2 = ctx.add_definition_var(x, x_val, ty=a)
        let b = readback(ctx2.values, ctx2.sig, ctx2.lvl(), b)
        eval(ctx2.values, ctx2.sig, b)
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
      let ctx2 = ctx.add_binding_var(x, ty=a_val)
      let (b, b_univ) = self.check_expr_is_type(ctx2, b)
      // TODO : temporarily rollback to type in type
      (Pi(TypedBinding((x, h, a)), b), VSet(0))
    }
    Hole(_) => {
      // insert ?t : ?a
      // TODO: In presence of a universe hierarchy, we should
      // insert a fresh level metavariable ?l with ?a : Set(?l)
      let a = eval(ctx.values, ctx.sig, self.fresh_meta(ctx, VSet(0)))
      let t = self.fresh_meta(ctx, a)
      (t, a)
    }
    Dot(_) => fail("dot expression should not be used in expression!")
  }
  let gamma = ctx.pp_gamma()
  let ty_expr = readback(ctx.values, ctx.sig, ctx.lvl(), ty)
  self.tracer.log(
    "infer! \{gamma} ⊢ \{expr.to_pretty()} ⇒ \{ty_expr.to_pretty()}",
  )
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
fn TyCtx::add_con(
  self : TyCtx,
  name : String,
  data_name : String,
  ty : TypeVal
) -> TyCtx {
  let con = ConDef::{ name, data_name, ty }
  { ..self, sig: { ..self.sig, cons: self.sig.cons.add(name, con) } }
}

///|
fn TyCtx::add_funclause(
  self : TyCtx,
  head : String,
  pats : Array[Pattern],
  rhs : Expr
) -> TyCtx raise Failure {
  // function clauses are not checked here, but in the elaboration phase
  let clause = Clause::{ lhs_head: head, lhs_pats: pats, rhs }
  match self.sig.constants.get(head) {
    Some(c) =>
      match c.definitions {
        Some(defs) => {
          defs.push(clause)
          self
        }
        None => {
          // create a new definition with the clause
          let defs = [clause]
          {
            ..self,
            sig: {
              ..self.sig,
              constants: self.sig.constants.add(head, ConstantDef::{
                ..c,
                definitions: Some(defs),
              }),
            },
          }
        }
      }
    None => fail("missing type signature of definition \{head}")
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
  let ty_expr = readback(ctx.values, ctx.sig, ctx.lvl(), tyval)
  self.tracer.log("axiom \{name} : \{ty_expr.to_pretty()}")
  if ctx.sig.constants.contains(name) && name != "_" {
    fail("axiom \{name} is already declaraed")
  }
  ctx.add_axiom(name, tyval)
}

///| Checking the telescope
fn Typer::check_telescope(
  self : Typer,
  ctx : TyCtx,
  telescope : @concrete.Telescope
) -> (TyCtx, Array[(String, TypeVal, Int)]) raise Failure {
  let mut ctx2 = ctx
  let binds = []
  for bind in telescope {
    match bind {
      TypedBinding((_, x, _, a)) => {
        let x = x.to_raw_name()
        let (a, a_univ) = self.check_expr_is_type(ctx, a)
        let a_val = eval(ctx.values, ctx.sig, a)
        binds.push((x, a_val, a_univ))
        ctx2 = ctx2.add_binding_var(x, ty=a_val)
      }
    }
  }
  (ctx2, binds)
}

///|
// fn Typer::data_check(
//   self : Typer,
//   ctx : TyCtx,
//   d : Name,
//   param : @concrete.Telescope,
//   ty : @concrete.Expr,
//   cons : Array[@concrete.Declaration]
// ) -> TyCtx raise Failure {
//   // data param : index -> sty
//   let (ctx2, _) = self.check_telescope(ctx, param)
//   let mut ctx2 = ctx2
//   let d_ty = @concrete.Expr::telescope_pi(param, ty)
//   let (d_ty, _) = self.infer(ctx2, d_ty)
//   let d_tyval = eval(ctx2.values, ctx2.sig, d_ty)
//   ctx2 = ctx2.add_axiom(d.to_raw_name(), d_tyval)
//   // constructors
//   for con in cons {
//     match con {
//       TypeSig(x, ty) => {
//         let (ty, _) = self.check_expr_is_type(ctx2, ty)
//         let tyval = eval(ctx2.values, ctx2.sig, ty)
//         ctx2 = ctx2.add_con(x.to_raw_name(), d.to_raw_name(), tyval)
//       }
//       _ => {
//         let r = con.get_range()
//         fail("at \{r} declaration is not a constructor type signature")
//       }
//     }
//   }
//   ctx2
// }

fn Typer::check_funclause(
  self : Typer,
  ctx : TyCtx,
  lhs : @concrete.Pattern,
  rhs : @concrete.Expr,
  whs : @concrete.WhereClause
) -> TyCtx raise Failure {
  // function clauses are not checked here, but in the elaboration phase
  let (lhs_head, lhs_pats) = match lhs {
    PIdent(f) => (f, List::Nil)
    PRawApp(_, Cons(PIdent(f), p, ps)) => (f, List::Cons(p, ps))
    PWild(r) => (Name::new(r, "_"), List::Nil)
    _ => fail("cannot parse the left hand side \{lhs} of function clause")
  }
  if not(ctx.sig.constants.contains(lhs_head.to_raw_name())) {

  }
  match ctx.sig.constants.get(lhs_head.to_raw_name()) {
    Some(c) => {
      guard lhs_pats.length() == 0 else {
        fail("pattern checking is not implemented yet")
      }
      let rhs = self.check(ctx, rhs, c.ty)
      ctx.add_funclause(lhs_head.to_raw_name(), [], rhs)
    }
    None => {
      let r = Range::merge_range(Range::merge_range(lhs, rhs), whs)
      fail("at \{r}, missing type signature of definition \{lhs_head}")
    }
  }
}

///|
fn Typer::check_postulate(
  self : Typer,
  ctx : TyCtx,
  kwr : @util.Range,
  ds : Array[@concrete.Declaration]
) -> TyCtx raise Failure {
  let mut ctx2 = ctx
  for d in ds {
    match d {
      TypeSig(x, ty) => {
        self.tracer.log("check declaration in postulate")
        self.tracer.log(d.to_pretty())
        ctx2 = self.axiom_check(ctx2, x, ty)
      }
      _ =>
        fail(
          "postulate at \{kwr} constains non-axiom declaration \{d.to_pretty()}",
        )
    }
  }
  ctx2
}

///|
fn Typer::check_declarations(
  self : Typer,
  ctx : TyCtx,
  decls : Array[@concrete.Declaration]
) -> Unit raise Failure {
  let mut ctx2 = ctx
  for decl in decls {
    self.tracer.log("\ncheck declaration")
    self.tracer.log(decl.to_pretty())
    match decl {
      TypeSig(x, ty) => ctx2 = self.axiom_check(ctx2, x, ty)
      FunClause(lhs, rhs, whs) =>
        ctx2 = self.check_funclause(ctx2, lhs, rhs, whs)
      DataDef(_, d, telescope, ty, cons) =>
        fail("data definition is not implemented yet")
      Postulate(kwr, ds) => ctx2 = self.check_postulate(ctx2, kwr, ds)
      Mutual(_) | Command(_) => fail("not implemented yet")
    }
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
