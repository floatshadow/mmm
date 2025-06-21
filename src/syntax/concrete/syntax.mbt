///|
typealias @syntax.Name

///|
typealias @syntax.Hiding

///| (x : e) or {xs : e}
pub(all) type TypedBinding (Range, Name, Hiding, Type) derive(Show)

///| \ x or \ {x}
pub(all) type UntypedBinding (Range, Name, Hiding) derive(Show)

///| (x : A) (y : B) (z : C) ... 
pub typealias Array[TypedBinding] as Telescope

///|
pub(all) type MetaVar Int derive(Eq, Hash)

///|
typealias @util.Range

///|
pub(all) enum Expr {
  Ident(Name)
  Set(Range, Int) // Set i
  Hole(Range) // underscore _
  Pi(TypedBinding, Type) // Π (x : A). B[x] or  Π {x : A}. B[x]
  Lam(UntypedBinding, Expr) // λ x . t or λ {x} . t
  RawApp(Range, Array[Expr]) // t1 t2 ... tn
  HiddenArg(Range, Name?, Expr) // {e} or {x = e}
  Dot(Range, Expr) // .p, only in patterns
} derive(Show)

///|
pub typealias Expr as Type

///|
pub(all) enum Pattern {
  PIdent(Name) // variable or constructor
  PRawApp(Range, Array[Pattern]) // p p1 p2 ... pn
  PHiddenArg(Range, Name?, Pattern) // {x} or {x = p}
  PWild(Range) // _ (wildcard pattern)
  PDot(Range, Expr) // inaccessible pattern .e
  PHidden(Range, Pattern)
} derive(Show)

///|
pub(all) enum WhereClause {
  NoWhere
  Where(Range, Array[Declaration])
} derive(Show)

///| Top level declarations.
pub(all) enum Declaration {
  Mutual(Range, Array[Declaration]) // mutual definition
  TypeSig(Name, Type) // f : A
  FunClause(Pattern, Expr, WhereClause)
  DataDef(Range, Name, Telescope, Type, Array[Declaration]) // data D : A where [c : A]
  Postulate(Range, Array[Declaration])
  Command(Range, Cmd)
} derive(Show)

///|
pub(all) enum Cmd {
  Normalize(Expr)
  InferType(Name)
  CheckCtx
} derive(Show)

///|
pub fn Expr::to_pattern(self : Expr) -> Pattern? {
  fn go(e : Expr) -> Pattern raise Error {
    match e {
      Ident(x) => PIdent(x)
      RawApp(r, es) => PRawApp(r, es.map(go))
      Hole(r) => PWild(r)
      Dot(r, e) =>
        match e {
          HiddenArg(r, x, e) => PHiddenArg(r, x, PDot(r, e))
          _ => PDot(r, e)
        }
      HiddenArg(r, x, e) => PHiddenArg(r, x, go(e))
      _ => fail("Cannot convert expression to pattern: \{e}")
    }
  }

  Some(go(self)) catch {
    _ => None
  }
}

///|
pub impl @util.HasRange for TypedBinding with get_range(self) {
  match self {
    TypedBinding((r, _, _, _)) => r
  }
}

///|
pub impl @util.HasRange for UntypedBinding with get_range(self) {
  match self {
    UntypedBinding((r, _, _)) => r
  }
}

///|
pub impl @util.HasRange for Expr with get_range(self) {
  match self {
    Ident(x) => x.get_range()
    Set(r, _) => r
    Hole(r) => r
    Pi(tbind, t) => Range::merge_range(tbind, t)
    Lam(utbind, e) => Range::merge_range(utbind, e)
    RawApp(r, _) => r
    HiddenArg(r, _, _) => r
    Dot(r, _) => r
  }
}

///|
pub impl @util.HasRange for Pattern with get_range(self) {
  match self {
    PIdent(x) => x.get_range()
    PRawApp(r, _) => r
    PHiddenArg(r, _, _) => r
    PWild(r) => r
    PDot(r, _) => r
    PHidden(r, _) => r
  }
}

///|
pub impl @util.HasRange for WhereClause with get_range(self) {
  match self {
    NoWhere => Range::NoRange
    Where(r, _) => r
  }
}

///|
pub impl @util.HasRange for Declaration with get_range(self) {
  match self {
    TypeSig(x, t) => Range::merge_range(x, t)
    FunClause(p, e, wc) => Range::merge_range(Range::merge_range(p, e), wc)
    DataDef(r, _, _, _, _) => r
    Mutual(r, _) => r
    Postulate(r, _) => r
    Command(r, _) => r
  }
}
