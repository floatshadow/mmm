///|
typealias @util.Range

///| 
pub struct Name {
  range : Range
  name : String
}

///|
pub fn Name::new(range : Range, name : String) -> Name {
  Name::{ name, range }
}

///|
pub fn Name::is_named(self : String) -> Bool {
  self == "_"
}

///|
pub fn Name::to_raw_name(self : Name) -> String {
  self.name
}

///|
pub(all) type DBId Int derive(Eq, Hash)

///|
pub(all) type DBlvl Int derive(Eq, Hash)

///| Implicit attribute..
pub(all) enum Hiding {
  Hiding // {x : A} or f {u}
  NotHiding // (x : A) or f u
} derive(Show, Eq)

///|
pub(all) enum Bounding {
  Bound
  Defined
} derive(Show, Eq)

///| e, (x = e) or {x = e}
pub(all) type NamedArg[T] (Range, Name?, Hiding, T)

///|
pub fn[A, B] NamedArg::fmap(
  self : NamedArg[A],
  f : (A) -> B raise
) -> NamedArg[B] raise {
  match self {
    NamedArg((r, x, hiding, v)) => NamedArg((r, x, hiding, f(v)))
  }
}

pub impl [T : Show] Show for NamedArg[T] with output(self, logger) {
  match self {
    NamedArg((_, Some(x), Hiding, e)) => {
      logger.write_string("{\{x} = ")
      Show::output(e, logger)
      logger.write_string("}")
    }
    NamedArg((_, None, Hiding, e)) => {
      logger.write_string("{")
      Show::output(e, logger)
      logger.write_string("}")
    }
    NamedArg((_, Some(x), NotHiding, e)) => {
      logger.write_string("\{x} = ")
      Show::output(e, logger)
    }
    NamedArg((_, None, NotHiding, e)) => Show::output(e, logger)
  }
}


///|
pub typealias @immut/hashmap.T[String, String] as NameMap

///|
pub typealias @immut/list.T[String] as NameList

///| Naive fresh name generator.
pub fn fresh_name(names : NameList) -> String {
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
pub impl Show for Name with output(self, logger) {
  logger.write_string(self.name)
}

///|
pub impl Eq for Name with op_equal(self, other) {
  self.name == other.name
}

///|
pub impl Hash for Name with hash_combine(self, h) {
  h.combine(self.name)
}

///|
pub impl @util.HasRange for Name with get_range(self) {
  self.range
}

///|
pub fn lvl2idx(n_free_vars : Int, x : DBlvl) -> DBId {
  DBId(n_free_vars - x.inner() - 1)
}

///|
pub impl Show for DBId with output(self, logger) {
  logger.write_string("#\{self.inner()}")
}

///|
pub impl Show for DBlvl with output(self, logger) {
  logger.write_string("ℓ\{self.inner()}")
}
