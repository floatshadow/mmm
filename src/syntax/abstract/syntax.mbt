///|
typealias @syntax.Hiding

///|
typealias @syntax.Bounding

///|
typealias @syntax.DBId

///|
typealias @immut/list.T as List

///|
pub(all) type TypedBinding (String, Hiding, Type)

///|
pub(all) type UntypedBinding (String, Hiding)

///| (x : A) (y : B) (z : C) ... 
pub typealias Array[TypedBinding] as Telescope

///|
pub(all) type MetaVar Int derive(Eq, Hash)

///|
pub(all) enum Expr {
  Var(DBId) // de Burijn index #1
  Def(String) // f
  Con(String) // c
  Set(Int) // Set i
  Pi(TypedBinding, Type) // Π (x : A). B[x] or  Π {x : A}. B[x]
  Lam(UntypedBinding, Expr) // λ x . t or λ {x} . t
  App(Expr, Expr, Hiding) // t1 t2 or t1 {t2}
  Let(Array[Declaration], Expr) // let x : A = t1 in t2
  Meta(MetaVar) // ?m
  InsertedMeta(MetaVar, List[Bounding]) // ?m [spine]
}

///|
pub typealias Expr as Type

///| p  ::=  x | c ps | .(e)
pub(all) enum Pattern {
  PVar(String)
  PCon(String, Array[Pattern])
  PDot(Expr) // inaccessible pattern
}

///| k  ::=  f ps = e
pub(all) struct Clause {
  lhs_head : String
  lhs_pats : Array[Pattern]
  rhs : Expr
}

///| Top level declarations.
pub(all) enum Declaration {
  Axiom(String, Type) // f : A
  Mutual(Array[Declaration]) // mutual definition
  Postulate(Array[Declaration]) // postulate f : A
  FunDef(String, Array[Clause])
  DataDef(String, Telescope, Type, Array[Declaration]) // data D : A where [c : A]
  Command(Cmd)
}

///|
pub(all) enum Cmd {
  Normalize(Expr)
  InferType(String)
  CheckCtx
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
pub impl Show for MetaVar with output(self, logger) {
  logger.write_string("?m\{self.inner()}")
}

///|
pub fn MetaVar::to_string(self : MetaVar) -> String {
  Show::to_string(self)
}

///|
pub impl Show for TypedBinding with output(self, logger) {
  match self {
    TypedBinding((name, imp, ty)) =>
      match imp {
        Hiding => {
          logger.write_string("{\{name} : ")
          logger.write_object(ty.to_pretty())
          logger.write_string("}")
        }
        NotHiding => {
          logger.write_string("(\{name} : ")
          logger.write_object(ty.to_pretty())
          logger.write_string(")")
        }
      }
  }
}

///|
pub impl Show for UntypedBinding with output(self, logger) {
  match self {
    UntypedBinding((name, imp)) =>
      match imp {
        Hiding => logger.write_string("{\{name}}")
        NotHiding => logger.write_string("\{name}")
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

///|
fn PrettyExpr::print_one_level(
  logger : @util.IndentLogger,
  syntax : Expr
) -> Unit {
  match syntax {
    Var(i) => logger.write_string("\{i}")
    Def(x) => logger.write_string("\{x}")
    Con(c) => logger.write_string("\{c}")
    Set(i) => logger.write_string("Set \{i}")
    Pi(tbind, return_ty) => {
      logger.write_string("\{tbind} → ")
      PrettyExpr::print_one_level(logger, return_ty)
    }
    Lam(utbind, body) => {
      logger.write_string("λ\{utbind}. ")
      PrettyExpr::print_one_level(logger, body)
    }
    App(func, arg, imp) => {
      PrettyExpr::print_one_level(logger, func)
      match imp {
        Hiding => {
          logger.write_string(" {")
          PrettyExpr::print_one_level(logger, arg)
          logger.write_string("}")
        }
        NotHiding => {
          logger.write_string(" ")
          PrettyExpr::print_one_level(logger, arg)
        }
      }
    }
    Let(decls, e) => {
      logger.write_string("let  ")
      logger.indent()
      for d in decls {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
      logger.write_string("in ")
      PrettyExpr::print_one_level(logger, e)
      logger.outdent()
    }
    Meta(mv) => logger.write_string("\{mv}")
    InsertedMeta(mv, spine) => {
      logger.write_string("\{mv} [")
      for bd in spine {
        match bd {
          Bound => logger.write_string("b")
          Defined => logger.write_string("d")
        }
      }
      logger.write_string("]")
    }
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
    PVar(name) => logger.write_string("\{name}")
    PCon(name, pats) => {
      logger.write_string("(\{name} ")
      for pat in pats {
        logger.write_string(" ")
        Show::output(pat, logger)
      }
      logger.write_string(")")
    }
    PDot(expr) => {
      logger.write_string(".(")
      Show::output(expr.to_pretty(), logger)
      logger.write_string(")")
    }
  }
}

///|
pub impl Show for Clause with output(self, logger) {
  logger.write_string("\{self.lhs_head} ")
  for pat in self.lhs_pats {
    logger.write_string(" ")
    Show::output(pat, logger)
  }
  logger.write_string(" = ")
  Show::output(self.rhs.to_pretty(), logger)
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
    Postulate(ds) => {
      logger.write_string("postulate\n")
      logger.indent()
      for d in ds {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
    }
    DataDef(d, tele, t, ds) => {
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
    FunDef(_, cs) =>
      for clause in cs {
        Show::output(clause, logger)
        logger.write_string("\n")
      }
    Axiom(x, t) => {
      logger.write_string("\{x} : ")
      PrettyExpr::print_one_level(logger, t)
    }
    Mutual(ds) => {
      logger.write_string("mutual\n")
      logger.indent()
      for d in ds {
        PrettyDecl::print_one_level(logger, d)
        logger.write_string("\n")
      }
      logger.outdent()
    }
    Command(cmd) => Show::output(cmd, logger)
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
