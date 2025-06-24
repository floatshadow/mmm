///|
typealias @immut/list.T as List

///| σ : Ren Γ Δ
/// Variable mapping from Γ to Δ in De Bruijn level.
pub struct Renaming {
  domain : Int
  codomain : Int
  rename : List[Int] //  Γ ⊢ σ : Δ
}

///| ε : Ren Γ ∙
pub fn Renaming::epsilon(domain : Int) -> Renaming {
  Renaming::{ domain, codomain: 0, rename: Nil }
}

///| _,_ : (σ : Ren Γ Δ) → Var Γ (A[σ]) → Ren Γ (Δ, A)
pub fn Renaming::extend(self : Renaming, var : Int) -> Renaming {
  Renaming::{
    domain: self.domain,
    codomain: self.codomain + 1,
    rename: self.rename.add(var),
  }
}

///|
pub struct Weaken {
  domain : Int
  codomain : Int
  weaken : List[Int]
}

///| ε    : Sub ∙ ∙
pub fn Weaken::epsilon() -> Weaken {
  Weaken::{ domain: 0, codomain: 0, weaken: Nil }
}

///| drop : Sub Γ Δ → Sub (Γ, A) Δ
pub fn Weaken::drop(self : Weaken) -> Weaken {
  Weaken::{
    domain: self.domain + 1,
    codomain: self.codomain,
    weaken: self.weaken,
  }
}

///| keep : (σ : Sub Γ Δ) → Sub (Γ, A[σ]) (Δ, A)
pub fn Weaken::keep(self : Weaken) -> Weaken {
  Weaken::{
    domain: self.domain + 1,
    codomain: self.codomain + 1,
    weaken: self.weaken.add(self.domain),
  }
}

/// inverse : (Δ : Context) → (spine : Subst Γ Δ) → Renaming Δ Γ
///
/// With pattern condition, the high-order unification problem
///   ?α spine =? rhs
/// has the unique solution `λ spine. rhs`
/// 
/// We have the following unification problem
///   Γ is the current context where `rhs` lives;
///   Δ is the cotext where the body of meta solution of `?a` lives.
///   Γ ⊢ ?α [spine] =? rhs
/// where
///   Δ ⊢ ?α : A  (_closing type_ • ⊢ ?α : Δ ⇒ A in definition 2.3, by Kovacs)
///   spine : Subst Γ Δ
///   Γ ⊢ rhs : A [spine]
///
/// We turn `spine` into a renaming mapping from
/// variables in `spine` under `Γ` to variables in solution `λ spine. rhs`
// pub fn inverse(env : VEnv, menv : MetaEnv, sig : Sig,
//    delta : Int,
//    spine : SpineView) -> Renaming!Failure {
//   let mut rename = Renaming::epsilon(delta)
//   let mut used = NameList::Nil
//   for arg in spine {
//     let (Nf(_, v), imp) = arg
//     match force_meta(env, menv, sig, v) {
//       VNe(_, NeRigid(x, [])) if not(used.contains(x)) => {
//         rename = rename.extend
//       }

//     }
//   }
//   rename
// }

///| Γ ⊢ ?α [spine] =? rhs
fn solve(
  env : VEnv,
  sig : Sig,
  names : NameList,
  mv : MetaVar,
  spine : Spine,
  rhs : Value
) -> Unit raise Failure {
  fail("not implemented: solve meta variable \{mv} with spine \{spine}")
}

///|
fn unify(
  env : VEnv,
  sig : Sig,
  names : NameList,
  v1 : TypeVal,
  v2 : TypeVal
) -> Unit raise Failure {
  let v1 = force_meta(env, sig, v1)
  let v2 = force_meta(env, sig, v2)
  match (v1, v2) {
    (VSet(u1), VSet(u2)) if u1 == u2 => ()
    (VLam(x1, h1, t1), VLam(x2, h2, t2)) if h1 == h2 => {
      let fresh_x = @syntax.fresh_name(names)
      let t1 = t1(VNe(Neutral::var(x1)))
      let t2 = t2(VNe(Neutral::var(x2)))
      let env2 = env.add((fresh_x, VNe(Neutral::var(fresh_x))))
      unify(env2, sig, names.add(fresh_x), t1, t2)
    }
    (t1, VLam(x2, h2, t2)) => {
      let fresh_x = @syntax.fresh_name(names)
      let t1 = eval_app(env, sig, t1, VNe(Neutral::var(fresh_x)), h2)
      let t2 = t2(VNe(Neutral::var(x2)))
      let env2 = env.add((fresh_x, VNe(Neutral::var(fresh_x))))
      unify(env2, sig, names.add(fresh_x), t1, t2)
    }
    (VLam(x1, h1, t1), t2) => {
      let fresh_x = @syntax.fresh_name(names)
      let t1 = t1(VNe(Neutral::var(fresh_x)))
      let t2 = eval_app(env, sig, t2, VNe(Neutral::var(fresh_x)), h1)
      let env2 = env.add((fresh_x, VNe(Neutral::var(fresh_x))))
      unify(env2, sig, names.add(fresh_x), t1, t2)
    }
    (VPi(x1, h1, a1, b1), VPi(x2, h2, a2, b2)) if h1 == h2 => {
      unify(env, sig, names, a1, a2)
      let fresh_x = @syntax.fresh_name(names)
      let b1 = b1(VNe(Neutral::var(fresh_x)))
      let b2 = b2(VNe(Neutral::var(fresh_x)))
      let env2 = env.add((fresh_x, VNe(Neutral::var(fresh_x))))
      unify(env2, sig, names.add(fresh_x), b1, b2)
    }
    (VNe(NeFlex(mv, sp)), v) => solve(env, sig, names, mv, sp, v)
    (v, VNe(NeFlex(mv, sp))) => solve(env, sig, names, mv, sp, v)
    _ => fail("unification failed: unify \{v1} with \{v2}")
  }
}
