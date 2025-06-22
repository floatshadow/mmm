///|
typealias @util.Loc

///|
typealias @syntax.Name

///|
typealias @syntax.Hiding

///|
typealias @syntax.Bounding

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
  Var(String)
  Set(Int) // Set i
  Pi(TypedBinding, Type) // Π (x : A). B[x] or  Π {x : A}. B[x]
  Lam(UntypedBinding, Expr) // λ x . t or λ {x} . t
  App(Expr, Expr, Hiding) // t1 t2 or t1 {t2}
  Let((String, Type), Expr, Expr) // let x : A = t1 in t2
  Meta(MetaVar) // ?m
  InsertedMeta(MetaVar, List[Bounding]) // ?m [spine]
  SrcPos(Loc, Expr) // debug
} derive(Show)

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
  Mutual(Array[Declaration]) // mutual definition
  FunDef(Name, Type, Array[Clause]) // f : A [ks]
  DataDef(Name, Telescope, Type, Array[(Name, Type)]) // data D : A where [c : A]
  Command(Cmd)
}

///|
pub(all) enum Cmd {
  Normalize(Expr)
  InferType(Name)
  CheckCtx
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
  self : PrettyExpr,
  logger : @util.IndentLogger,
  syntax : Expr
) -> Unit {
  match syntax {
    Var(name) => logger.write_string("\{name}")
    Set(i) => logger.write_string("Set \{i}")
    Pi(tbind, return_ty) => {
      logger.write_string("\{tbind} -> ")
      self.print_one_level(logger, return_ty)
    }
    Lam(utbind, body) => {
      logger.write_string("λ \{utbind} . ")
      self.print_one_level(logger, body)
    }
    App(func, arg, imp) => {
      self.print_one_level(logger, func)
      match imp {
        Hiding => {
          logger.write_string(" {")
          self.print_one_level(logger, arg)
          logger.write_string("}")
        }
        NotHiding => {
          logger.write_string(" ")
          self.print_one_level(logger, arg)
        }
      }
    }
    Let((x, x_typ), e1, e2) => {
      logger.write_string("let \{x} : ")
      self.print_one_level(logger, x_typ)
      logger.write_string(" = ")
      match e1 {
        Let(_, _, _) => {
          logger.write_string("\n")
          logger.indent()
          self.print_one_level(logger, e1)
          logger.outdent()
        }
        _ => self.print_one_level(logger, e1)
      }
      logger.write_string("\n")
      logger.indent()
      self.print_one_level(logger, e2)
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
    SrcPos(_, inner) => self.print_one_level(logger, inner)
  }
}

///|
pub impl Show for PrettyExpr with output(self, logger) {
  let logger = @util.IndentLogger::new(logger)
  self.print_one_level(logger, self.syntax)
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
