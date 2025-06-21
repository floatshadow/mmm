fn raw_application(exprs : List1[Expr]) -> Expr {
  match exprs {
    Cons(head, Nil) => head
    _ as es => RawApp(es.get_range(), es.to_array())
  }
}


fn funclause_or_typesig(raw_lhs : Expr, mrhs : Either[Expr, Type], wh : WhereClause) -> Declaration {
  let lhs = match raw_lhs.to_pattern() {
    Some(lhs) => lhs
    None => abort("Cannot convert expression \{raw_lhs} to pattern")
  }
  match mrhs {
    Left(rhs) => {
      FunClause(lhs, rhs, wh)
    }
    Right(ty) => {
      let x = match lhs {
        PIdent(x) => x
        PWild(r) => Name::new(r, "_")
        _ => abort("LHS \{raw_lhs} is not a single identifier")
      }
      TypeSig(x, ty)
    }
  }
}
