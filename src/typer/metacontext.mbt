///|
pub enum MetaEntry {
  Solved(Value, TypeVal)
  Unsolved(TypeVal)
} derive(Show)

// Global meta variable environment.
///|
pub struct MetaEnv {
  mut next_meta : Int
  metas : @hashmap.T[MetaVar, MetaEntry]
}

///|
pub fn MetaEnv::new() -> MetaEnv {
  MetaEnv::{ next_meta: 0, metas: @hashmap.new() }
}

///|
pub fn MetaEnv::reset(self : MetaEnv) -> Unit {
  self.next_meta = 0
  self.metas.clear()
}

///|
pub fn MetaEnv::next_meta(self : MetaEnv) -> MetaVar {
  let meta = self.next_meta
  self.next_meta += 1
  MetaVar(meta)
}

///|
pub fn MetaEnv::find(self : MetaEnv, mv : MetaVar) -> MetaEntry? {
  self.metas.get(mv)
}
