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
typealias @syntax.NameList

///| match one pattern against a value.
fn match_pat(env : VEnv, pat : Pattern, v : Value) -> VEnv? {
  match (pat, v) {
    (PDot(_), _) => Some(env)
    (PVar(x), _) => Some(env.add((x, v)))
    (PCon(name, []), VNe(NeCon(con, []))) if name == con => Some(env)
    (PCon(name, pats), VNe(NeCon(con, spine))) if name == con =>
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
    ([pat, .. pats], [(v, _), .. vs]) if match_pat(env, pat, v) is Some(env2) =>
      match_pats(env2, pats, vs)
    _ => None
  }
}

///|
fn match_clause(
  env : VEnv,
  sig : Sig,
  clause : Clause,
  spine : SpineView
) -> Value? raise Failure {
  let pats = clause.lhs_pats
  let rhs = clause.rhs
  if spine.length() < pats.length() {
    return None
  }
  let matched_spine = spine[0:pats.length()]
  let unmatched_spine = spine[pats.length():]
  match match_pats(env, pats, matched_spine) {
    Some(env2) =>
      Some(eval_app_spine(env2, sig, eval(env2, sig, rhs), unmatched_spine))
    None => None
  }
}

///|
fn match_clauses(
  env : VEnv,
  sig : Sig,
  clauses : Array[Clause],
  spine : SpineView
) -> Value? raise Failure {
  fn go(clauses : ArrayView[Clause]) -> Value? raise Failure {
    match clauses {
      [] => None
      [clause, .. clauses] =>
        match match_clause(env, sig, clause, spine) {
          Some(v) => Some(v)
          None => go(clauses)
        }
    }
  }

  go(clauses)
}

///| beta/iota-reduction
fn eval_app(
  env : VEnv,
  sig : Sig,
  f : Value,
  v : Value,
  vh : Hiding
) -> Value raise Failure {
  match f {
    VLam(_, h, t) => {
      guard h == vh else {
        fail(
          "expected an \{h} argument but an \{vh} argument applies in 'eval_app'",
        )
      }
      t(v)
    }
    VNe(ne) =>
      match ne {
        NeRigid(name, spine) => VNe(NeRigid(name, extend_spine(spine, v, vh)))
        NeFlex(mv, spine) => VNe(NeFlex(mv, extend_spine(spine, v, vh)))
        NeDef(name, spine) => {
          guard sig.constants.get(name) is Some(fun_def) else {
            fail("does not find function \{name} in signature")
          }
          let spine2 = extend_spine(spine, v, vh)
          match fun_def.definitions {
            Some(clauses) if match_clauses(env, sig, clauses, spine2) is Some(v) =>
              v
            _ => VNe(NeDef(name, spine2))
          }
        }
        NeCon(name, spine) => VNe(NeCon(name, extend_spine(spine, v, vh)))
      }
    _ => fail("not a function like value in 'eval_app'")
  }
}

///|
fn eval_app_spine(
  env : VEnv,
  sig : Sig,
  f_val : Value,
  spine : SpineView
) -> Value raise Failure {
  let mut head = f_val
  for arg in spine {
    let (arg_val, imp) = arg
    head = eval_app(env, sig, head, arg_val, imp)
  }
  head
}

///|
fn eval_meta(mv : MetaVar) -> Value raise Failure {
  match lookup_meta(mv) {
    Some(MetaEntry::Solved(v, ..)) => v
    Some(MetaEntry::Unsolved(_)) =>
      // Unsolved meta variable, return a neutral value.
      VNe(Neutral::meta(mv))
    None => fail("does not find meta variable \{mv} in metacontext")
  }
}

///|
fn eval_app_bds(
  env : VEnv,
  sig : Sig,
  m : Value,
  bds : List[Bounding]
) -> Value raise Failure {
  match (env, bds) {
    (_, Nil) => m
    (Cons((_, t), env), Cons(Bound, bds)) =>
      eval_app(env, sig, eval_app_bds(env, sig, m, bds), t, Hiding::NotHiding)
    (Cons(_, env), Cons(Defined, bds)) => eval_app_bds(env, sig, m, bds)
    _ => fail("the environment \{env} and the bounding \{bds} do not match")
  }
}

///|
fn force_meta(env : VEnv, sig : Sig, value : Value) -> Value raise Failure {
  match value {
    VNe(NeFlex(mv, spine)) if lookup_meta(mv) is Some(Solved(v, ..)) =>
      force_meta(env, sig, eval_app_spine(env, sig, v, spine))
    _ => value
  }
}

///|
pub fn eval(env : VEnv, sig : Sig, expr : Expr) -> Value raise Failure {
  match expr {
    Var(ix) =>
      match env.nth(ix.inner()) {
        Some((_, v)) => v
        None => fail("does not find variable \{ix} in environment \{env}")
      }
    // eagerly try to expand definitions
    Def(f) => {
      guard sig.constants.get(f) is Some(fun_def) else {
        fail("does not find function \{f} in signature")
      }
      match fun_def.definitions {
        Some(clauses) if match_clauses(env, sig, clauses, []) is Some(v) => v
        _ => VNe(NeDef(f, []))
      }
    }
    Con(c) => VNe(Neutral::con(c))
    Meta(mv) => eval_meta(mv)
    Set(i) => VSet(i)
    Pi(TypedBinding((x, h, a)), b) => {
      let a = eval(env, sig, a)
      fn b_tyval(x_val) -> Value raise Failure {
        eval(env.add((x, x_val)), sig, b)
      }

      VPi(x, h, a, b_tyval)
    }
    Lam(UntypedBinding((x, h)), t) => {
      fn t_val(x_val) -> Value raise Failure {
        eval(env.add((x, x_val)), sig, t)
      }

      VLam(x, h, t_val)
    }
    App(f, arg, h) => {
      let f = eval(env, sig, f)
      let arg = eval(env, sig, arg)
      eval_app(env, sig, f, arg, h)
    }
    InsertedMeta(mv, bds) => eval_app_bds(env, sig, eval_meta(mv), bds)
    Let(_) => fail("let expression is not supported in evaluation")
  }
}

// Reading back value to expressions.
// Generate fresh name for normalization given used names.

///|
fn readback_neutral(
  env : VEnv,
  sig : Sig,
  n_free_vars : Int,
  ntr : Neutral
) -> Expr raise Failure {
  fn readback_spine(head : Expr, spine : Spine) -> Expr raise Failure {
    let mut app = head
    for named_arg in spine {
      match named_arg {
        (v, h) => {
          let arg = readback(env, sig, n_free_vars, v)
          app = App(app, arg, h)
        }
      }
    }
    app
  }

  match ntr {
    NeRigid(x, spine) =>
      readback_spine(Var(@syntax.lvl2idx(n_free_vars, x)), spine)
    NeFlex(mv, spine) => readback_spine(Meta(mv), spine)
    NeCon(name, spine) => readback_spine(Con(name), spine)
    NeDef(name, spine) => readback_spine(Def(name), spine)
  }
}

///|
pub fn readback(
  env : VEnv,
  sig : Sig,
  free_vars : Int,
  value : Value
) -> Expr raise Failure {
  // println("readback: \{value} in free vars \{free_vars}")
  match force_meta(env, sig, value) {
    VLam(x, h, t) => {
      // Functions
      // λx. t / neutral value
      // Generate a symbolic argument (neutral variable `x`)
      // to trigger the normalization of body `t`.
      let x_val = VNe(Neutral::vvar(free_vars))
      Lam(
        UntypedBinding((x, h)),
        readback(env.add((x, x_val)), sig, free_vars + 1, t(x_val)),
      )
    }
    VPi(x, h, a, b) => {
      let x_val = VNe(Neutral::vvar(free_vars))
      Pi(
        TypedBinding((x, h, readback(env, sig, free_vars, a))),
        readback(env.add((x, x_val)), sig, free_vars + 1, b(x_val)),
      )
    }
    VSet(i) => Set(i)
    VNe(ntr) => readback_neutral(env, sig, free_vars, ntr)
  }
}
