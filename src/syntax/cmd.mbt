/// Top level declarations.
pub(all) enum Declaration {
  Mutual(Array[Declaration]) // mutual definition
  FunDef(Name, Type, Array[Clause]) // f : A [ks]
  DataDef(Name, Telescope, Type, Array[(Name, Type)]) // data D : A where [c : A]
  Command(Cmd)
}

pub(all) enum Cmd {
  Normalize(Expr)
  InferType(Name)
  CheckCtx
}