// Normalization by evaluation.
// Substitution based normalization simply repeatedly applies β-reduction.
// NbE does normalization in a way of interpreting the term.
// Major problems in developing NbE:
//  - Term may contains free variables, how to eval such open terms?
//    f a -> (fun x -> ...) a, but f may get stuck (neutral form)
//    Solution: we admit free variables as a value.
//  - Admit free variables as value would ban further evaluations.
//    f arg1 arg2 ... ->
//
// In typed NbE, each type can specify its own notion of equality, 
// and thus the syntax of its normal forms. Therefore, reading back 
// is now recursive on the structure of the type rather than 
// the structure of the value.
// 
// Checking Dependent Types with Normalization by Evaluation: A Tutorial (Haskell Version)
// David Thrane Christiansen (2019)
///|
typealias @abstract.Pattern

///|
typealias @abstract.TypedBinding

///| match one pattern against a value.
fn match_pat(env : VEnv, pat : Pattern, v : Value) -> VEnv? {
  match (pat, v) {
    (PDot(_), _) => Some(env)
    (PVar(x), _) => Some(env.add((Some(x), v)))
    (PCon(name, []), VNe(_, NeCon(con, []))) if name == con => Some(env)
    (PCon(name, pats), VNe(_, NeCon(con, spine))) if name == con =>
      match_pats(env, pats, spine)
    _ => None
  }
}

///| match a list of patterns against a spine.
fn match_pats(
  env : VEnv,
  pats : ArrayView[Pattern],
  spine : SpineView
) -> VEnv? {
  match (pats, spine) {
    ([], []) => Some(env)
    ([pat, .. pats], [(Nf(_, v), imp), .. vs]) =>
      match match_pat(env, pat, v) {
        Some(env2) => match_pats(env2, pats, vs)
        None => None
      }
    _ => None
  }
}

///|
fn match_clause(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  clause : Clause,
  spine : SpineView
) -> Value?!Failure {
  let pats = clause.lhs_pats
  let rhs = clause.rhs
  guard spine.length() == pats.length() else {
    fail!("arity of pattern \{pats} patterns and spine \{spine} does not match")
  }
  match match_pats(env, pats, spine) {
    Some(env2) => Some(eval!(env2, menv, sig, rhs))
    None => None
  }
}

///|
fn match_clauses(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  clauses : Array[Clause],
  spine : SpineView
) -> Value?!Failure {
  fn go(clauses : ArrayView[Clause]) -> Value?!Failure {
    match clauses {
      [] => None
      [clause, .. clauses] =>
        match match_clause!(env, menv, sig, clause, spine) {
          Some(v) => Some(v)
          None => go(clauses)
        }
    }
  }

  go!(clauses)
}

///| beta/iota-reduction
fn eval_app(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  f_val : Value,
  arg_val : Value,
  imp : Imp
) -> Value!Failure {
  match f_val {
    VLam(x_imp, body_val) => {
      if x_imp != imp {
        fail!(
          "expected an \{x_imp} argument but an \{imp} argument applies in 'eval_app'",
        )
      }
      body_val!(arg_val)
    }
    VNe(VPi(x_imp, a, b), ne) => {
      if x_imp != imp {
        fail!(
          "expected an \{x_imp} argument but an \{imp} argument applies in 'eval_app'",
        )
      }
      let b_val = b!(arg_val)
      let nf = Nf(a, arg_val)
      match ne {
        NeRigid(name, spine) =>
          VNe(b_val, NeRigid(name, extend_spine(spine, nf, imp)))
        NeFlex(mv, spine) =>
          VNe(b_val, NeFlex(mv, extend_spine(spine, nf, imp)))
        NeDef(name, spine) => {
          guard sig.funs.get(name) is Some(fun_def) else {
            fail!("does not find function \{name} in signature")
          }
          let clauses = fun_def.clauses
          let spine2 = extend_spine(spine, nf, imp)
          // delta/iota-reduction
          if clauses.length() == spine2.length() {
            match match_clauses!(env, menv, sig, clauses, spine2) {
              Some(v) => v
              None => VNe(b_val, NeDef(name, spine2))
            }
          } else {
            VNe(b_val, NeDef(name, spine2))
          }
        }
        NeCon(name, spine) => {
          let spine2 = extend_spine(spine, nf, imp)
          VNe(b_val, NeCon(name, spine2))
        }
        NeData(name, spine) => {
          let spine2 = extend_spine(spine, nf, imp)
          VNe(b_val, NeData(name, spine2))
        }
      }
    }
    _ => fail!("not a function like value in 'eval_app'")
  }
}

///|
fn eval_app_spine(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  f_val : Value,
  spine : SpineView
) -> Value!Failure {
  let mut head = f_val
  for arg in spine {
    let (Nf(_, arg_val), imp) = arg
    head = eval_app!(env, menv, sig, head, arg_val, imp)
  }
  head
}

///|
fn eval_meta(mv : MetaVar, menv : MetaEnv) -> Value!Failure {
  match menv.find(mv) {
    Some(MetaEntry::Solved(val, _)) => val
    Some(MetaEntry::Unsolved(typ)) => {
      // Unsolved meta variable, return a neutral value.
      let ne = Neutral::meta(mv)
      VNe(typ, ne)
    }
    None => fail!("does not find meta variable \{mv} in metacontext")
  }
}

///| variable in the raw expression may be a 
/// free variable, function, or constructor.
fn eval_var(x : String, env : VEnv, sig : Sig) -> Value!Failure {
  match env.lookup(Some(x)) {
    Some(v) => v
    None =>
      match sig.funs.get(x) {
        Some(f) => VNe(f.ty, Neutral::def(f.name))
        None =>
          match sig.datas.get(x) {
            Some(d) => VNe(d.ty, Neutral::data(d.name))
            None =>
              match sig.cons.get(x) {
                Some(c) => VNe(c.ty, Neutral::con(c.name))
                None => fail!("does not find \{x} in env when evaluation!")
              }
          }
      }
  }
}

///|
pub fn eval(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  expr : Expr
) -> Value!Failure {
  match expr {
    Var(x) => eval_var!(x, env, sig)
    Meta(mv) => eval_meta!(mv, menv)
    Set(i) => VSet(i)
    Pi(TypedBinding((param_name, imp, param_ty)), res_ty) => {
      let param_tyval = eval!(env, menv, sig, param_ty)
      fn res_tyval(param_val) -> Value!Failure {
        eval!(env.add((param_name, param_val)), menv, sig, res_ty)
      }

      VPi(imp, param_tyval, res_tyval)
    }
    Lam(param_name, imp, body) => {
      fn body_val(param_val) -> Value!Failure {
        eval!(env.add((Some(param_name), param_val)), menv, sig, body)
      }

      VLam(imp, body_val)
    }
    App(f, arg, imp) => {
      let f_val = eval!(env, menv, sig, f)
      let arg_val = eval!(env, menv, sig, arg)
      eval_app!(env, menv, sig, f_val, arg_val, imp)
    }
    Let((x, _), e1, e2) => {
      let e1_val = eval!(env, menv, sig, e1)
      eval!(env.add((Some(x), e1_val)), menv, sig, e2)
    }
  }
}

// Reading back value to expressions.
// Generate fresh name for normalization given used names.
///|
fn fresh_name(names : NameList) -> String {
  loop 0 {
    i => {
      let name = "x\{i}"
      if names.contains(name) {
        continue i + 1
      } else {
        break name
      }
    }
  }
}

///|
fn readback_neutral(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  ntr : Neutral,
  names : NameList
) -> Expr!Failure {
  fn readback_spine(
    head : Expr,
    spine : Spine,
    names : NameList
  ) -> Expr!Failure {
    let mut app = head
    for nf in spine {
      match nf {
        (nf, imp) => {
          let arg = readback!(env, menv, sig, nf, names)
          app = App(app, arg, imp)
        }
      }
    }
    app
  }

  match ntr {
    NeRigid(x, spine) => readback_spine!(Var(x), spine, names)
    NeFlex(mv, spine) => readback_spine!(Meta(mv), spine, names)
  }
}

///|
pub fn readback_type(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  typ : TypeVal,
  names : NameList
) -> Expr!Failure {
  match typ {
    VSet(i) => Set(i)
    VPi(imp, param_tyval, res_tyval) => {
      let name = fresh_name(names)
      let param_typ = readback_type!(env, menv, sig, param_tyval, names)
      let param_ty_value = VNe(param_tyval, Neutral::var(name))
      let return_typ = readback_type!(
        env,
        menv,
        sig,
        res_tyval!(param_ty_value),
        names.add(name),
      )
      Pi(@abstract.TypedBinding((Some(name), imp, param_typ)), return_typ)
    }
    VNe(_, ntr) => readback_neutral!(env, menv, sig, ntr, names)
    _ => fail!("\{typ} is not a type in 'readback_type'")
  }
}

///|
pub fn readback(
  env : VEnv,
  menv : MetaEnv,
  sig : Sig,
  nf : Normal,
  names : NameList
) -> Expr!Failure {
  match nf {
    Nf(VPi(imp, a, b), f_value) => {
      // Functions
      // λx. t / neutral value
      // Generate a symbolic argument (neutral variable `x`)
      // to trigger the normalization of body `t`.
      let x_name = fresh_name(names)
      let x_val = VNe(a, Neutral::var(x_name))
      let body_tyval = b!(x_val)
      let body_val = eval_app!(env, menv, sig, f_value, x_val, imp)
      // Wrap the body with lambda abstraction, i.e., η-expansion.
      Lam(
        x_name,
        imp,
        readback!(env, menv, sig, Nf(body_tyval, body_val), names.add(x_name)),
      )
    }
    Nf(VSet(_), value) => readback_type!(env, menv, sig, value, names)
    Nf(nf_typ, VNe(ntr_typ, ntr)) => {
      if not(types_equiv!(nf_typ, ntr_typ, names)) {
        fail!("neutral type mismatch in readback: \{nf_typ} != \{ntr_typ}")
      }
      readback_neutral!(env, menv, sig, ntr, names)
    }
    _ => fail!("\{nf} is ill-typed normal form in 'readback'")
  }
}
