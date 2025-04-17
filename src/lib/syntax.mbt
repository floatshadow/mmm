///|
pub(all) enum Syntax {
  Var(String)
  Set(Int) // Set i
  Pi(String, Syntax, Syntax) // Π (x : A). B[x]
  Lam(String, Syntax, Syntax) // λ (x : A). t
  App(Syntax, Syntax) // t1 t2
  // Let((String, Syntax), Syntax, Syntax) // let x : A = t1 in t2
  // LetRec((String, Syntax), Syntax, Syntax) // let rec f : (x1 : A1) -> (x2 : A2) -> .. (xn : An) -> B = t1 in t2
} derive(Show, Eq)

pub typealias Type = Syntax