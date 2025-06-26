///|
typealias @syntax.Name

///|
typealias @syntax.Hiding

typealias @syntax.NamedArg

///| (x : e) or {xs : e}
pub(all) type TypedBinding (Range, Name, Hiding, Type)

///| \ x or \ {x}
pub(all) type UntypedBinding (Range, Name, Hiding)

///| (x : A) (y : B) (z : C) ... 
pub typealias Array[TypedBinding] as Telescope

///|
pub(all) type MetaVar Int derive(Eq, Hash)

///|
typealias @util.Range

///|
typealias @util.List2

///|
pub(all) enum Expr {
  Ident(Name)
  Set(Range, Int) // Set i
  Hole(Range) // underscore _
  Pi(TypedBinding, Type) // Π (x : A). B[x] or  Π {x : A}. B[x]
  Lam(UntypedBinding, Expr) // λ x . t or λ {x} . t
  RawApp(Range, List2[Expr]) // t1 t2 ... tn
  App(Range, Expr, NamedArg[Expr]) // t1 t2
  HiddenArg(Range, Name?, Expr) // {e} or {x = e}
  Dot(Range, Expr) // .p, only in patterns
}

///|
pub typealias Expr as Type

///|
pub(all) enum Pattern {
  PIdent(Name) // variable or constructor
  PRawApp(Range, List2[Pattern]) // p p1 p2 ... pn
  PHiddenArg(Range, Name?, Pattern) // {x} or {x = p}
  PWild(Range) // _ (wildcard pattern)
  PDot(Range, Expr) // inaccessible pattern .e
}

///|
pub(all) enum WhereClause {
  NoWhere
  Where(Range, Array[Declaration])
}

///| Top level declarations.
pub(all) enum Declaration {
  Mutual(Range, Array[Declaration]) // mutual definition
  TypeSig(Name, Type) // f : A
  FunClause(Pattern, Expr, WhereClause)
  DataDef(Range, Name, Telescope, Type, Array[Declaration]) // data D : A where [c : A]
  Postulate(Range, Array[Declaration])
  Command(Range, Cmd)
}

///|
pub(all) enum Cmd {
  Normalize(Expr)
  InferType(Name)
  CheckCtx
}

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
      _ => fail("Cannot convert expression to pattern: \{e.to_pretty()}")
    }
  }

  Some(go(self)) catch {
    _ => None
  }
}

///|
pub fn Expr::split_pi(self : Expr) -> (Telescope, Type) {
  loop ([], self) {
    (telescope, Pi(tbind, codomain)) => {
      telescope.push(tbind)
      continue (telescope, codomain)
    }
    (telescope, ty) => break (telescope, ty)
  }
}

///|
pub fn Expr::telescope_pi(telescope : Telescope, codomain : Type) -> Type {
  let mut ty = codomain
  for tbind in telescope.rev() {
    ty = Pi(tbind, ty)
  }
  ty
}

///|
pub fn Pattern::to_expr(self : Pattern) -> Expr {
  fn go(p : Pattern) -> Expr {
    match p {
      PIdent(x) => Ident(x)
      PRawApp(r, ps) => RawApp(r, ps.map(go))
      PWild(r) => Hole(r)
      PDot(_, e) => e
      PHiddenArg(r, x, p) => HiddenArg(r, x, go(p))
    }
  }

  go(self)
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
    App(r, _, _) => r
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

///|
pub impl Show for TypedBinding with output(self, logger) {
  match self {
    TypedBinding((_, x, imp, ty)) =>
      match imp {
        Hiding => {
          logger.write_string("{\{x} : ")
          logger.write_object(ty.to_pretty())
          logger.write_string("}")
        }
        NotHiding => {
          logger.write_string("(\{x} : ")
          logger.write_object(ty.to_pretty())
          logger.write_string(")")
        }
      }
  }
}

///|
pub impl Show for UntypedBinding with output(self, logger) {
  match self {
    UntypedBinding((_, x, imp)) =>
      match imp {
        Hiding => logger.write_string("{\{x}}")
        NotHiding => logger.write_string("\{x}")
      }
  }
}

///|
pub fn TypedBinding::to_string(self : TypedBinding) -> String {
  Show::to_string(self)
}

///|
pub struct PrettyExpr {
  syntax : Expr
}

///|
pub fn Expr::to_pretty(self : Expr) -> PrettyExpr {
  PrettyExpr::{ syntax: self }
}

pub impl Show for Expr with output(self, logger) {
  let logger = @util.IndentLogger::new(logger)
  PrettyExpr::print_one_level(logger, self)
}

///|
fn PrettyExpr::print_one_level(
  logger : @util.IndentLogger,
  syntax : Expr
) -> Unit {
  match syntax {
    Ident(x) => logger.write_string("\{x}")
    Set(_, i) => logger.write_string("Set \{i}")
    Pi(bind, return_ty) => {
      logger.write_string("\{bind}")
      logger.write_string(" → ")
      PrettyExpr::print_one_level(logger, return_ty)
    }
    Lam(utbind, body) => {
      logger.write_string("λ\{utbind}")
      logger.write_string(". ")
      PrettyExpr::print_one_level(logger, body)
    }
    RawApp(_, es) =>
      for e in es {
        logger.write_string("(")
        PrettyExpr::print_one_level(logger, e)
        logger.write_string(")")
        logger.write_string(" ")
      }
    App(_, e1, e2) => {
      logger.write_string("(")
      PrettyExpr::print_one_level(logger, e1)
      logger.write_string(") (")
      Show::output(e2, logger)
      logger.write_string(")")
    }
    Hole(_) => logger.write_string("?_")
    HiddenArg(_, Some(name), e) => {
      logger.write_string("{\{name} = ")
      PrettyExpr::print_one_level(logger, e)
      logger.write_string("}")
    }
    HiddenArg(_, None, e) => {
      logger.write_string("{")
      PrettyExpr::print_one_level(logger, e)
      logger.write_string("}")
    }
    Dot(_, e) => PrettyExpr::print_one_level(logger, e)
  }
}

///|
pub impl Show for PrettyExpr with output(self, logger) {
  let logger = @util.IndentLogger::new(logger)
  PrettyExpr::print_one_level(logger, self.syntax)
}

///|
pub impl Show for Pattern with output(self, logger) {
  match self {
    PDot(_) => logger.write_string(".")
    PWild(_) => logger.write_string("_")
    PHiddenArg(_, Some(x), p) => {
      logger.write_string("{\{x} = ")
      Show::output(p, logger)
      logger.write_string("}")
    }
    PHiddenArg(_, None, p) => {
      logger.write_string("{")
      Show::output(p, logger)
      logger.write_string("}")
    }
    PRawApp(_, ps) =>
      for p in ps {
        logger.write_string("(")
        Show::output(p, logger)
        logger.write_string(")")
        logger.write_string(" ")
      }
    PIdent(x) => logger.write_string("\{x}")
  }
}

///|
pub impl Show for Cmd with output(self, logger) {
  match self {
    Normalize(e) => {
      logger.write_string(":NORMALIZE ")
      logger.write_object(e.to_pretty())
    }
    InferType(x) => logger.write_string(":INFER \{x}")
    CheckCtx => logger.write_string(":CHECK CTX")
  }
}

///|
pub struct PrettyDecl {
  decl : Declaration
}

///|
pub fn Declaration::to_pretty(self : Declaration) -> PrettyDecl {
  PrettyDecl::{ decl: self }
}

///|
fn PrettyDecl::print_one_level(
  logger : @util.IndentLogger,
  decl : Declaration
) -> Unit {
  match decl {
    Postulate(_, ds) => {
      logger.write_string("postulate\n")
      logger.indent()
      for d in ds {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
    }
    DataDef(_, d, tele, t, ds) => {
      logger.write_string("data \{d} ")
      for tbind in tele {
        logger.write_string("\{tbind} ")
      }
      logger.write_string(" : ")
      PrettyExpr::print_one_level(logger, t)
      logger.write_string(" where\n")
      logger.indent()
      for d in ds {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
    }
    FunClause(p, e, wh) => {
      Show::output(p, logger)
      logger.write_string(" = ")
      PrettyExpr::print_one_level(logger, e)
      match wh {
        NoWhere => ()
        Where(_, ds) => {
          logger.write_string("\n")
          logger.indent()
          logger.write_string("where\n")
          for d in ds {
            PrettyDecl::print_one_level(logger, d)
            logger.write_string("\n")
          }
          logger.outdent()
        }
      }
    }
    TypeSig(x, t) => {
      logger.write_string("\{x} : ")
      PrettyExpr::print_one_level(logger, t)
    }
    Mutual(_, ds) => {
      logger.write_string("mutual\n")
      logger.indent()
      for d in ds {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
    }
    Command(_, cmd) => Show::output(cmd, logger)
  }
}

///|
pub impl Show for PrettyDecl with output(self, logger) {
  let logger = @util.IndentLogger::new(logger)
  PrettyDecl::print_one_level(logger, self.decl)
}

///|
pub struct PrettyDecls {
  decls : Array[Declaration]
}

///|
pub fn PrettyDecls::new(decls : Array[Declaration]) -> PrettyDecls {
  PrettyDecls::{ decls, }
}

///|
pub impl Show for PrettyDecls with output(self, logger) {
  for ds in self.decls {
    Show::output(ds.to_pretty(), logger)
    logger.write_string("\n")
  }
}
