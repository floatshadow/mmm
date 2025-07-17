///|
typealias @util.List2

///| 
fn raw_application(exprs : List1[Expr]) -> Expr {
  match exprs {
    Cons(e, Nil) => e
    Cons(e1, Cons(e2, es1)) as es =>
      RawApp(es.get_range(), List2::Cons(e1, e2, es1))
  }
}

///|
fn funclause_or_typesig(
  raw_lhs : Expr,
  mrhs : Either[Expr, Type],
  wh : WhereClause
) -> Declaration {
  let lhs = match raw_lhs.to_pattern() {
    Some(lhs) => lhs
    None => abort("Cannot convert expression \{raw_lhs.to_pretty()} to pattern")
  }
  match mrhs {
    Left(rhs) => FunClause(lhs, rhs, wh)
    Right(ty) => {
      let x = match lhs {
        PIdent(x) => x
        PWild(r) => Name::new(r, "_")
        _ => abort("LHS \{raw_lhs.to_pretty()} is not a single identifier")
      }
      TypeSig(x, ty)
    }
  }
}
