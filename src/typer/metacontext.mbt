///|
typealias @hashmap.T as MutMap

///|
pub enum MetaEntry {
  Solved(TypeVal, Value)
  Unsolved(TypeVal)
} derive(Show)

// Global meta variable environment.

///|
let next_meta : Ref[Int] = Ref::new(0)

///|
let metas : MutMap[MetaVar, MetaEntry] = @hashmap.new()

///|
pub fn fresh_meta(tyctx : TyCtx) -> @abstract.Expr {
  let meta = next_meta.val
  next_meta.val += 1
  @abstract.InsertedMeta(MetaVar(meta), tyctx.boundings())
}

///|
pub fn lookup_meta(mv : MetaVar) -> MetaEntry? {
  metas.get(mv)
}

///|
pub fn get_menv() -> MutMap[MetaVar, MetaEntry] {
  metas
}

///|
pub fn unsolved_metas() -> Array[(MetaVar, TypeVal)] {
  let unsolved = []
  for meta_info in metas {
    let (mv, entry) = meta_info
    match entry {
      MetaEntry::Unsolved(ty) => unsolved.push((mv, ty))
      _ => ()
    }
  }
  unsolved
}

///|
pub fn pretty_menv(logger : @util.IndentLogger) -> Unit {
  logger.write_string("Θ = ")
  for meta_info in metas {
    let (mv, entry) = meta_info
    match entry {
      Solved(ty, val) => logger.write_string("\{mv} : \{ty} = \{val}, ")
      Unsolved(ty) => logger.write_string("\{mv} : \{ty} (unsolved), ")
    }
  }
}
