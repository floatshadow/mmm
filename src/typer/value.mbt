///|
using @abstract {type MetaVar}

///|
using @syntax {type Hiding}

///|
using @syntax {type Name}

///|
using @abstract {type Clause}

///|
using @abstract {type Telescope}

///|
type Spine = Array[(Value, Hiding)]

///|
type SpineView = ArrayView[(Value, Hiding)]

///|
pub fn extend_spine(spine : Spine, nf : Value, imp : Hiding) -> Spine {
  let spine2 = spine.copy()
  spine2.push((nf, imp))
  spine2
}

///|
type VEnv = @util.List[(String, Value)]

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
type Map[K, V] = @immut_hashmap.HashMap[K, V]

///|
/// Signature Σ
pub struct Sig {
  constants : Map[String, ConstantDef]
  datas : Map[String, DataDef]
  cons : Map[String, ConDef]
} derive(Show)

///|
pub fn Sig::new() -> Sig {
  Sig::{
    constants: @immut_hashmap.new(),
    datas: @immut_hashmap.new(),
    cons: @immut_hashmap.new(),
  }
}

///|
// The name "rigid" comes from the fact that in unification.
// unify two different rigid value raises an error;
// unify a rigid and a flexible value solves meta variable.
pub enum Neutral {
  NeRigid(DBlvl, Spine) // local variable applied to spine, e.g., l [spine]
  NeFlex(MetaVar, Spine) // meta variable applied to spine, e.g., ?m [spine]
  NeCon(String, Spine) // c es
  NeDef(String, Spine) // delta/iota-redex f es
} derive(Show)

///|
#alias(TypeVal)
pub enum Value {
  VNe(Neutral) // neutral
  VSet(Int) // universe
  VPi(String, Hiding, Value, (Value) -> Value raise Failure) // HOAS
  VLam(String, Hiding, (Value) -> Value raise Failure) // HOAS
} derive(Show)

///|
pub fn Neutral::vvar(lvl : Int) -> Neutral {
  NeRigid(DBlvl(lvl), [])
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
