///|
typealias @syntax.MetaVar

///|
typealias @syntax.Imp

///|
typealias @syntax.Name

///|
typealias @syntax.Clause

///|
typealias @syntax.Telescope

///|
typealias Spine = Array[(Normal, Imp)]

///|
typealias SpineView = ArrayView[(Normal, Imp)]

///|
pub fn extend_spine(spine : Spine, nf : Normal, imp : Imp) -> Spine {
  let spine2 = spine.copy()
  spine2.push((nf, imp))
  spine2
}

///|
typealias Value as TypeVal

///|
typealias VEnv = @immut/list.T[(Name?, Value)]

///|
pub struct FunDef {
  name : Name
  ty : TypeVal
  clauses : Array[Clause]
} derive(Show)

///|
pub struct DataDef {
  name : Name
  param : Telescope
  ty : TypeVal
} derive(Show)

///|
pub struct ConDef {
  name : Name
  data_name : Name
  ty : TypeVal
} derive(Show)

///|
pub struct Sig {
  funs : @immut/hashmap.T[Name, FunDef]
  datas : @immut/hashmap.T[Name, DataDef]
  cons : @immut/hashmap.T[Name, ConDef]
} derive(Show)

///|
// The name "rigid" comes from the fact that in unification.
// unify two different rigid value raises an error;
// unify a rigid and a flexible value solves meta variable.
pub enum Neutral {
  NeRigid(Name, Spine) // local variable applied to spine, e.g., l [spine]
  NeFlex(MetaVar, Spine) // meta variable applied to spine, e.g., ?m [spine]
  NeCon(Name, Spine) // c es
  NeDef(Name, Spine) // delta/iota-redex f es
  NeData(Name, Spine) // D ps es
} derive(Show)

///|
pub enum Value {
  VNe(TypeVal, Neutral) // neutral
  VSet(Int) // universe
  VPi(Imp, Value, (Value) -> Value!Failure) // HOAS
  VLam(Imp, (Value) -> Value!Failure) // HOAS
} derive(Show)

///|
pub enum Normal {
  Nf(TypeVal, Value)
} derive(Show)

///|
pub fn Neutral::var(name : String) -> Neutral {
  NeRigid(name, [])
}

///|
pub fn Neutral::meta(mv : MetaVar) -> Neutral {
  NeFlex(mv, [])
}

///|
pub fn Neutral::con(name : Name) -> Neutral {
  NeCon(name, [])
}

///|
pub fn Neutral::def(name : Name) -> Neutral {
  NeDef(name, [])
}

///|
pub fn Neutral::data(name : String) -> Neutral {
  NeData(name, [])
}
