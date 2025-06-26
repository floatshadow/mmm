///|
typealias @immut/list.T as List

///| σ : Ren Γ Δ
/// Variable mapping from Γ to Δ in de Bruijn level.
pub struct Renaming {
  dom : Int
  codom : Int
  // Γ ⊢ σ : Δ, mapping from variables in Δ to variables in Γ
  ren : List[Int]
}

///| ε : Ren Γ ∙
pub fn Renaming::epsilon(dom : Int) -> Renaming {
  Renaming::{ dom, codom: 0, ren: Nil }
}

///| _,_ : (σ : Ren Γ Δ) → Var Γ (A[σ]) → Ren Γ (Δ, A)
pub fn Renaming::extend(self : Renaming, lvl : Int) -> Renaming {
  Renaming::{ dom: self.dom, codom: self.codom + 1, ren: self.ren.add(lvl) }
}

///|
pub struct Weaken {
  dom : Int
  codom : Int
  weaken : List[Int]
}

///| ε    : Sub ∙ ∙
pub fn Weaken::epsilon() -> Weaken {
  Weaken::{ dom: 0, codom: 0, weaken: Nil }
}

///| drop : Sub Γ Δ → Sub (Γ, A) Δ
pub fn Weaken::drop(self : Weaken) -> Weaken {
  Weaken::{ dom: self.dom + 1, codom: self.codom, weaken: self.weaken }
}

///| keep : (σ : Sub Γ Δ) → Sub (Γ, A[σ]) (Δ, A)
pub fn Weaken::keep(self : Weaken) -> Weaken {
  Weaken::{
    dom: self.dom + 1,
    codom: self.codom + 1,
    weaken: self.weaken.add(self.dom),
  }
}

///|
pub struct PartialRenaming {
  dom : Int
  codom : Int
  // Γ ⊢ σ : Δ, mapping from variables in Δ to variables in Γ
  ren : Map[Int, Int]
}

///|
pub fn PartialRenaming::lift(self : PartialRenaming) -> PartialRenaming {
  PartialRenaming::{
    dom: self.dom + 1,
    codom: self.codom + 1,
    ren: self.ren.add(self.codom, self.dom),
  }
}

///| inverse : (Γ : Context) → (spine : Subst Δ Γ) → Renaming Γ Δ
///
/// With pattern condition, the high-order unification problem
///   ?α spine =? rhs
/// has the unique solution `λ spine. rhs`
/// 
/// We have the following unification problem
///   Γ is the current context where `rhs` lives;
///   Δ is the cotext where the body of meta solution of `?a` lives.
///   Γ ⊢ ?α [spine] =? rhs : A
/// where
///   Δ ⊢ ?α : A  (_closing type_ • ⊢ ?α : Δ ⇒ A in definition 2.3, by Kovacs)
///   spine : Subst Γ Δ
///   Γ ⊢ rhs : A [spine]
///
/// We turn `spine` into a renaming mapping from
/// variables in `spine` under `Γ` to variables in solution `λ spine. rhs`
fn inverse(
  env : VEnv,
  sig : Sig,
  gamma : Int,
  spine : SpineView
) -> PartialRenaming raise Failure {
  fn go(sp : SpineView) -> (Int, Map[Int, Int]) raise Failure {
    match sp {
      [] => (0, @immut/hashmap.new())
      [.. vs, (v, _)] => {
        let (delta, ren) = go(vs)
        match force_meta(env, sig, v) {
          VNe(NeRigid(lvl, [])) => {
            let x = lvl.inner()
            match ren.get(lvl.inner()) {
              None => (delta + 1, ren.add(lvl.inner(), delta))
              Some(_) =>
                fail(
                  "cannot invert spine \{spine}: variable of de Burijn level \{x} already in renaming",
                )
            }
          }
          v =>
            fail(
              "cannot invert spine \{spine}: expected a variable, but got \{v}",
            )
        }
      }
    }
  }

  let (delta, ren) = go(spine)
  PartialRenaming::{ dom: delta, codom: gamma, ren }
}

///|
fn rename(
  mv : MetaVar,
  pren : PartialRenaming,
  rhs : Value
) -> Expr raise Failure {
  letrec go_spine = fn(
    pren : PartialRenaming,
    hd : Expr,
    sp : SpineView
  ) -> Expr raise Failure {
    match sp {
      [] => hd
      [.. vs, (v, h)] => {
        let t = go_spine(pren, hd, vs)
        let u = go(pren, v)
        App(t, u, h)
      }
    }
  }
  and go = fn(pren : PartialRenaming, v : Value) -> Expr raise Failure {
    match v {
      VNe(NeFlex(mv2, spine)) =>
        if mv == mv2 {
          fail("metavariable \{mv} appears in rhs \{rhs}")
        } else {
          go_spine(pren, Meta(mv2), spine)
        }
      VNe(NeRigid(lvl, sp)) => {
        let x = lvl.inner()
        match pren.ren.get(x) {
          Some(x) => go_spine(pren, Var(@syntax.lvl2idx(pren.dom, x)), sp)
          None =>
            fail(
              "In rhs \{rhs}, variable of de Burijn level \{x} not found in renaming",
            )
        }
      }
      VNe(NeCon(name, sp)) => go_spine(pren, Con(name), sp)
      VNe(NeDef(name, sp)) => go_spine(pren, Def(name), sp)
      VSet(i) => Set(i)
      VPi(x, h, a, b) => {
        let a = go(pren, a)
        let b = go(pren.lift(), b(VNe(Neutral::vvar(pren.codom))))
        Pi(TypedBinding((x, h, a)), b)
      }
      VLam(x, h, t) => {
        let t = go(pren.lift(), t(VNe(Neutral::vvar(pren.codom))))
        Lam(UntypedBinding((x, h)), t)
      }
    }
  }

  go(pren, rhs)
}

///| Γ ⊢ ?α [spine] =? rhs
fn Typer::solve(
  self : Typer,
  env : VEnv,
  sig : Sig,
  lvl : Int,
  mv : MetaVar,
  spine : Spine,
  rhs : Value
) -> Unit raise Failure {
  self.tracer.log("\{lvl} ⊢ \{mv} [\{spine}] = \{rhs}")
  let pren = inverse(env, sig, lvl, spine)
  let rhs = rename(mv, pren, rhs)
  let mut lam = rhs
  for delta_lvl, arg in spine.iter2() {
    let (_, h) = arg
    lam = Lam(UntypedBinding(("x#\{delta_lvl}", h)), lam)
  }
  let solution = eval(Nil, sig, lam)
  let mty = match lookup_meta(mv) {
    Some(MetaEntry::Unsolved(mty~)) => mty
    Some(MetaEntry::Solved(_)) => fail("meta variable \{mv} already solved!")
    _ => fail("meta variable \{mv} not found in metacontext")
  }
  self.tracer.log("  solution \{mv} [spine] : \{mty} = \{lam.to_pretty()}")
  metas.set(mv, MetaEntry::Solved(mty~, solution))
}

///|
fn Typer::unify_spine(
  self : Typer,
  env : VEnv,
  sig : Sig,
  lvl : Int,
  sp1 : SpineView,
  sp2 : SpineView
) -> Unit raise Failure {
  match (sp1, sp2) {
    ([], []) => ()
    ([.. vs1, (t1, h1)], [.. vs2, (t2, h2)]) => {
      guard h1 == h2 else {
        fail("cannot unify spine: (\{t1}, \{h1}) with (\{t2}, \{h2})")
      }
      self.unify_spine(env, sig, lvl, vs1, vs2)
      self.unify(env, sig, lvl, t1, t2)
    }
    _ => fail("cannot unify spine: \{sp1} with \{sp2}")
  }
}

///|
fn Typer::unify(
  self : Typer,
  env : VEnv,
  sig : Sig,
  lvl : Int,
  v1 : TypeVal,
  v2 : TypeVal
) -> Unit raise Failure {
  self.tracer.log("unify \{v1} with \{v2} [\{@syntax.DBlvl(lvl)}]")
  let v1 = force_meta(env, sig, v1)
  let v2 = force_meta(env, sig, v2)
  match (v1, v2) {
    (VSet(u1), VSet(u2)) if u1 == u2 => ()
    (VLam(x1, h1, t1), VLam(x2, h2, t2)) if h1 == h2 => {
      let t1 = t1(VNe(Neutral::vvar(lvl)))
      let t2 = t2(VNe(Neutral::vvar(lvl)))
      let env2 = env.add((bind_name(x1, x2), VNe(Neutral::vvar(lvl))))
      self.unify(env2, sig, lvl + 1, t1, t2)
    }
    (t1, VLam(x2, h2, t2)) => {
      let t1 = eval_app(env, sig, t1, VNe(Neutral::vvar(lvl)), h2)
      let t2 = t2(VNe(Neutral::vvar(lvl)))
      let env2 = env.add((x2, VNe(Neutral::vvar(lvl))))
      self.unify(env2, sig, lvl + 1, t1, t2)
    }
    (VLam(x1, h1, t1), t2) => {
      let t1 = t1(VNe(Neutral::vvar(lvl)))
      let t2 = eval_app(env, sig, t2, VNe(Neutral::vvar(lvl)), h1)
      let env2 = env.add((x1, VNe(Neutral::vvar(lvl))))
      self.unify(env2, sig, lvl + 1, t1, t2)
    }
    (VSet(i), VSet(j)) if i == j => ()
    (VPi(x1, h1, a1, b1), VPi(x2, h2, a2, b2)) if h1 == h2 => {
      self.unify(env, sig, lvl, a1, a2)
      let b1 = b1(VNe(Neutral::vvar(lvl)))
      let b2 = b2(VNe(Neutral::vvar(lvl)))
      let env2 = env.add((bind_name(x1, x2), VNe(Neutral::vvar(lvl))))
      self.unify(env2, sig, lvl + 1, b1, b2)
    }
    (VNe(NeFlex(mv, sp)), v) => self.solve(env, sig, lvl, mv, sp, v)
    (v, VNe(NeFlex(mv, sp))) => self.solve(env, sig, lvl, mv, sp, v)
    (VNe(NeRigid(lvl1, sp1)), VNe(NeRigid(lvl2, sp2))) if lvl1 == lvl2 =>
      self.unify_spine(env, sig, lvl, sp1, sp2)
    (VNe(NeCon(c1, sp1)), VNe(NeCon(c2, sp2))) if c1 == c2 =>
      self.unify_spine(env, sig, lvl, sp1, sp2)
    (VNe(NeDef(d1, sp1)), VNe(NeDef(d2, sp2))) if d1 == d2 =>
      self.unify_spine(env, sig, lvl, sp1, sp2)
    _ => fail("unification failed: \{v1} != \{v2}")
  }
}

///|
fn Typer::unify_err(
  self : Typer,
  env : VEnv,
  sig : Sig,
  lvl : Int,
  v1 : TypeVal,
  v2 : TypeVal
) -> Unit raise Failure {
  let t1 = readback(env, sig, lvl, v1)
  let t2 = readback(env, sig, lvl, v2)
  self.tracer.log(
    "\{t1.to_pretty()} =? \{t2.to_pretty()} [\{@syntax.DBlvl(lvl)}]",
  )
  self.unify(env, sig, lvl, v1, v2)
}
