///|
typealias @abstract.MetaVar

///|
typealias @syntax.Hiding

///|
typealias @syntax.Name

///|
typealias @abstract.Clause

///|
typealias @abstract.Telescope

///|
typealias Array[(Value, Hiding)] as Spine

///|
typealias ArrayView[(Value, Hiding)] as SpineView

///|
pub fn extend_spine(spine : Spine, nf : Value, imp : Hiding) -> Spine {
  let spine2 = spine.copy()
  spine2.push((nf, imp))
  spine2
}

///|
typealias Value as TypeVal

///|
typealias @immut/list.T[(String, Value)] as VEnv

///|
pub struct ConstantDef {
  name : String
  ty : TypeVal
  definitions : Array[Clause]?
} derive(Show)

///|
pub struct DataDef {
  name : String
  param : Telescope
  ty : TypeVal
} derive(Show)

///|
pub struct ConDef {
  name : String
  data_name : String
  ty : TypeVal
} derive(Show)

///|
typealias @immut/hashmap.T as Map

///| Signature Σ
pub struct Sig {
  constants : Map[String, ConstantDef]
  datas : Map[String, DataDef]
  cons : Map[String, ConDef]
} derive(Show)

///|
pub fn Sig::new() -> Sig {
  Sig::{
    constants: @immut/hashmap.new(),
    datas: @immut/hashmap.new(),
    cons: @immut/hashmap.new(),
  }
}

///|
// The name "rigid" comes from the fact that in unification.
// unify two different rigid value raises an error;
// unify a rigid and a flexible value solves meta variable.
pub enum Neutral {
  NeRigid(String, Spine) // local variable applied to spine, e.g., l [spine]
  NeFlex(MetaVar, Spine) // meta variable applied to spine, e.g., ?m [spine]
  NeCon(String, Spine) // c es
  NeDef(String, Spine) // delta/iota-redex f es
  NeData(String, Spine) // D ps es
} derive(Show)

///|
pub enum Value {
  VNe(Neutral) // neutral
  VSet(Int) // universe
  VPi(String, Hiding, Value, (Value) -> Value raise Failure) // HOAS
  VLam(String, Hiding, (Value) -> Value raise Failure) // HOAS
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
pub fn Neutral::con(name : String) -> Neutral {
  NeCon(name, [])
}

///|
pub fn Neutral::def(name : String) -> Neutral {
  NeDef(name, [])
}

///|
pub fn Neutral::data(name : String) -> Neutral {
  NeData(name, [])
}
