///|
typealias Syntax = @types.Syntax

///|
typealias TypeVal = Value

///|
typealias VEnv = @immut/hashmap.T[String, Value]

///|
typealias NameMap = @immut/hashmap.T[String, String]

///|
typealias NameList = @immut/list.T[String]

// Normalization by evaluation.
// Substitution based normalization simply repeatedly applies β-reduction.
// NbE does normalization in a way of interpreting the term.
// Major problems in developing NbE:
//  - Term may contains free variables, how to eval such open terms?
//    f a -> (fun x -> ...) a, but f may get stuck (neutral form)
//    Solution: we admit free variables as a value.
//  - Admit free variables as value would ban further evaluations.
//    f arg1 arg2 ... ->
///|
pub enum Value {
  VNe(Neutral)
  VSet(Int)
  VPi(Value, (Value) -> Value!Failure) // HOAS
  VLam((Value) -> Value!Failure)
} derive(Show)

///|
pub enum Neutral {
  NeVar(String)
  NeApp(Neutral, Value)
} derive(Show)

///|
pub fn eval(env : VEnv, expr : Syntax) -> Value!Failure {
  match expr {
    Var(x) =>
      match env.find(x) {
        Some(v) => v
        None => fail!("does not find \{x} in env when evaluation!")
      }
    Set(i) => VSet(i)
    Pi(param_name, param_ty, return_ty) => {
      let param_ty_value = eval!(env, param_ty)
      fn return_ty_value(param_value) -> Value!Failure {
        eval!(env.add(param_name, param_value), return_ty)
      }

      VPi(param_ty_value, return_ty_value)
    }
    Lam(param_name, body) => {
      fn body_value(param_value) -> Value!Failure {
        eval!(env.add(param_name, param_value), body)
      }

      VLam(body_value)
    }
    App(func, arg) =>
      match eval!(env, func) {
        VLam(f) => f!(eval!(env, arg))
        VNe(ne) => VNe(NeApp(ne, eval!(env, arg)))
        fval => fail!("\{fval} is not a function like value in 'eval'")
      }
    Let((x, _), e1, e2) => {
      let e1_value = eval!(env, e1)
      eval!(env.add(x, e1_value), e2)
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
pub fn readback(value : Value, names : NameList) -> Syntax!Failure {
  match value {
    VNe(NeVar(x)) => Var(x)
    VNe(NeApp(f, arg)) => {
      let f = readback!(VNe(f), names)
      let arg = readback!(arg, names)
      App(f, arg)
    }
    VSet(i) => Set(i)
    VPi(param_ty_value, return_ty_func) => {
      // original param name may coincide with variables in env
      let name = fresh_name(names)
      Pi(
        name,
        readback!(param_ty_value, names),
        readback!(return_ty_func!(VNe(NeVar(name))), names.add(name)),
      )
    }
    VLam(body_func) => {
      // λx. t
      // Generate a symbolic argument (neutral variable `x`)
      // to trigger the normalization of body `t`
      let name = fresh_name(names)
      // Wrap the body with lambda abstraction.
      Lam(name, readback!(body_func!(VNe(NeVar(name))), names.add(name)))
    }
  }
}

///|
fn normalize(env : VEnv, expr : Syntax) -> Syntax!Failure {
  let env_names = []
  for nval in env {
    let (name, _) = nval
    env_names.push(name)
  }
  let used_names = @immut/list.from_array(env_names)
  readback!(eval!(env, expr), used_names)
}

///|
fn types_equiv(
  value1 : TypeVal,
  value2 : TypeVal,
  names : NameList
) -> Bool!Failure {
  let expr1 = readback!(value1, names)
  let expr2 = readback!(value2, names)
  expr1 == expr2
}

///|
pub struct TyCtx {
  values : VEnv
  typs : VEnv
  names : NameList
}

///|
pub fn TyCtx::empty() -> TyCtx {
  TyCtx::{
    values: @immut/hashmap.new(),
    typs: @immut/hashmap.new(),
    names: Nil,
  }
}

///|
pub fn TyCtx::add_neutral_var(
  self : TyCtx,
  name : String,
  typ : Value
) -> TyCtx {
  // Free variables in Γ are neutral values 
  // since we don't know their values.
  let value = VNe(NeVar(name))
  TyCtx::{
    values: self.values.add(name, value),
    typs: self.typs.add(name, typ),
    names: self.names.add(name),
  }
}

///|
pub fn TyCtx::add_var(
  self : TyCtx,
  name : String,
  value : Value,
  typ : TypeVal
) -> TyCtx {
  // In let binding, we would obtain the value of
  // variable in Γ, so we can use it as a value.
  TyCtx::{
    values: self.values.add(name, value),
    typs: self.typs.add(name, typ),
    names: self.names.add(name),
  }
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
// Γ |- e <= A
// --------------- (T-Anno)
// Γ |- e : A => A 
// 
// Γ |- e => A   Γ |- A ≡ B
// ------------------------ (T-Conv)
// Γ |- e <= B

///|
fn check_expr_is_type(ctx : TyCtx, expr : Syntax) -> Int!Failure {
  match infer!(ctx, expr) {
    VSet(i) => i
    _ => fail!("\{expr} is not a type universe")
  }
}

///|
pub fn check(ctx : TyCtx, expr : Syntax, typ : Value) -> Unit!Failure {
  // println("check \{expr} <= \{typ}")
  match expr {
    // A ~> (x : B) -> C[x]   Γ, x : B |- e : C[x] ~ t
    // ------------------------------------------
    // Γ |- λx. e <= A ~ λx. t
    Lam(param_name, body) =>
      match typ {
        VPi(expected_param_ty_value, expected_return_ty_func) => {
          let neutral_param_value = VNe(NeVar(param_name))
          let ctx2 = ctx.add_var(
            param_name, neutral_param_value, expected_param_ty_value,
          )
          let expected_return_ty = expected_return_ty_func!(neutral_param_value)
          check!(ctx2, body, expected_return_ty)
        }
        _ => fail!("\{typ} is not a dependent function type")
      }
    Let((x, x_typ), e1, e2) => {
      let _ = check_expr_is_type!(ctx, x_typ)
      let x_typ_value = eval!(ctx.values, x_typ)
      let _ = check!(ctx, e1, x_typ_value)
      let e1_value = eval!(ctx.values, e1)
      let ctx2 = ctx.add_var(x, e1_value, x_typ_value)
      check!(ctx2, e2, typ)
    }
    // Γ |- e => B  A = B
    // -------------------
    // Γ |- e <= A
    _ => {
      let infer_ty_value = infer!(ctx, expr)
      // check if inferred type is equal to given type
      if not(types_equiv!(infer_ty_value, typ, ctx.names)) {
        fail!("expected \{expr} : \{infer_ty_value}, but got \{typ}")
      }
    }
  }
}

///|
pub fn infer(ctx : TyCtx, expr : Syntax) -> Value!Failure {
  // println("infer \{expr}")
  let typ_val = match expr {
    // (x : A) ∈ Γ
    // ------------
    // Γ |- x => A
    Var(x) =>
      match ctx.typs.find(x) {
        Some(typ) => typ
        None => fail!("does not find \{x} in env when inference!")
      }
    // -------------------------
    // Γ |- Set i => Set (i + 1)
    Set(i) => VSet(i + 1)
    // Γ |- e1 => A -> B  Γ, x : A |- e2 <= A
    // ---------------------------------------
    // Γ |- e1 e2 => B[x |-> t]
    App(f, arg) => {
      let infer_f_ty = infer!(ctx, f)
      match infer_f_ty {
        VPi(param_ty_value, return_ty_func) => {
          check!(ctx, arg, param_ty_value)
          return_ty_func!(eval!(ctx.values, arg))
        }
        _ => fail!("\{f} is not of (dependent) function type")
      }
    }
    Lam(_) => fail!("unable to infer a lambda term")
    // Γ |- A => Set i  Γ, x : A |- B[x] => Set j
    // -----------------------------------------
    // Γ |- Π (x : A). B[x] => Set (max(i, j))
    Pi(param_name, param_ty, return_ty) => {
      // println("infer Pi \{param_name} : \{param_ty} => \{return_ty}")
      let param_universe = check_expr_is_type!(ctx, param_ty)
      let param_ty_value = eval!(ctx.values, param_ty)
      let ctx2 = ctx.add_neutral_var(param_name, param_ty_value)
      let return_universe = check_expr_is_type!(ctx2, return_ty)
      VSet(@math.maximum(param_universe, return_universe))
    }
    // Γ |- e1 <= A  Γ, x : A |- e2 => B
    // ----------------------------------
    // Γ |- let x : A = e1 in e2 => B
    Let((x, x_typ), e1, e2) => {
      let _ = check_expr_is_type!(ctx, x_typ)
      let x_typ_value = eval!(ctx.values, x_typ)
      // println("let \{x}: \{x_typ_value}")
      let _ = check!(ctx, e1, x_typ_value)
      let e1_value = eval!(ctx.values, e1)
      // println("let \{x} = \{e1_value}")
      let ctx2 = ctx.add_var(x, e1_value, x_typ_value)
      infer!(ctx2, e2)
    }
  }
  // println("inferred \{expr} => \{typ_val}")
  typ_val
}

///|
pub fn alpha_equiv(maps : NameMap, expr1 : Syntax, expr2 : Syntax) -> Bool {
  match (expr1, expr2) {
    (Var(name1), Var(name2)) =>
      match maps.get(name1) {
        Some(n) => n == name2
        None => name1 == name2
      }
    (Set(u1), Set(u2)) => u1 == u2
    (Pi(n1, p1, r1), Pi(n2, p2, r2)) =>
      alpha_equiv(maps, p1, p2) && alpha_equiv(maps.add(n1, n2), r1, r2)
    (Lam(n1, b1), Lam(n2, b2)) => alpha_equiv(maps.add(n1, n2), b1, b2)
    (App(f1, a1), App(f2, a2)) =>
      alpha_equiv(maps, f1, f2) && alpha_equiv(maps, a1, a2)
    _ => false
  }
}
