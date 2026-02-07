///|
type MutMap[K, V] = @hashmap.HashMap[K, V]

///|
pub enum MetaEntry {
  Solved(mty~ : TypeVal, Value)
  Unsolved(mty~ : TypeVal)
} derive(Show)

// Global meta variable environment.

///|
let next_meta : Ref[Int] = Ref::new(0)

///|
let metas : MutMap[MetaVar, MetaEntry] = @hashmap.new()

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
      MetaEntry::Unsolved(mty~) => unsolved.push((mv, mty))
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
      Solved(mty~, val) => logger.write_string("\{mv} = \{val} : \{mty}, ")
      Unsolved(mty~) => logger.write_string("\{mv} : \{mty} (unsolved), ")
    }
  }
}
