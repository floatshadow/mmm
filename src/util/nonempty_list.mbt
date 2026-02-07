///|
using @immut/list {type T as List}

///|
/// Moonbit core has not transferred List::map to error polymorphic version yet.
fn[A, B] map_exn(xs : List[A], f : (A) -> B raise?) -> List[B] raise? {
  match xs {
    Nil => Nil
    Cons(hd, tl) => Cons(f(hd), map_exn(tl, f))
  }
}

///|
pub(all) enum List1[A] {
  Cons(A, List[A])
} derive(Eq)

///|
/// Extract the first element of the non-empty list.
pub fn[A] List1::head(self : List1[A]) -> A {
  match self {
    Cons(hd, _) => hd
  }
}

///|
/// Extract the possibly-empty tail of the non-empty list.
pub fn[A] List1::tail(self : List1[A]) -> List[A] {
  match self {
    Cons(_, tl) => tl
  }
}

///|
pub fn[A] List1::cons(self : List1[A], value : A) -> List1[A] {
  match self {
    Cons(hd, tl) => Cons(value, Cons(hd, tl))
  }
}

///|
/// Get the length of the list.
pub fn[A] List1::length(self : List1[A]) -> Int {
  match self {
    Cons(_, tl) => 1 + tl.length()
  }
}

///|
pub fn[A, B] List1::map(
  self : List1[A],
  f : (A) -> B raise?,
) -> List1[B] raise? {
  match self {
    Cons(hd, tl) => Cons(f(hd), map_exn(tl, f))
  }
}

///|
pub fn[A] List1::each(self : List1[A], f : (A) -> Unit) -> Unit {
  match self {
    Cons(hd, tl) => {
      f(hd)
      tl.each(f)
    }
  }
}

///|
pub fn[A] List1::all(self : List1[A], f : (A) -> Bool) -> Bool {
  match self {
    Cons(hd, tl) => if f(hd) { tl.all(f) } else { false }
  }
}

///|
pub fn[A] List1::any(self : List1[A], f : (A) -> Bool raise) -> Bool raise {
  match self {
    Cons(hd, tl) => f(hd) || tl.any(f)
  }
}

///|
pub fn[A, B] List1::fold(self : List1[A], init~ : B, f : (B, A) -> B) -> B {
  match self {
    Cons(hd, tl) => tl.fold(init=f(init, hd), f)
  }
}

///|
pub fn[A] List1::from_list(xs : List[A]) -> List1[A]? {
  match xs {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A] List1::from_array(arr : Array[A]) -> List1[A]? {
  if arr.length() == 0 {
    None
  } else {
    for i = arr.length() - 1, list = List::Nil; i > 0; {
      continue i - 1, List::Cons(arr[i], list)
    } else {
      Some(Cons(arr[0], list))
    }
  }
}

///|
pub fn[A] List1::to_list(self : List1[A]) -> List[A] {
  match self {
    Cons(hd, tl) => Cons(hd, tl)
  }
}

///|
pub fn[A] List1::to_array(self : List1[A]) -> Array[A] {
  let arr = []
  match self {
    Cons(hd, tl) => {
      arr.push(hd)
      loop tl {
        Nil => ()
        Cons(hd, tl) => {
          arr.push(hd)
          continue tl
        }
      }
      arr
    }
  }
}

///|
pub fn[A] List1::concat(self : List1[A], other : List1[A]) -> List1[A] {
  match self {
    Cons(hd, tl) => Cons(hd, tl.concat(other.to_list()))
  }
}

///|
pub fn[A] List1::rev_concat(self : List1[A], other : List1[A]) -> List1[A] {
  match self {
    Cons(hd, Nil) => Cons(hd, other.to_list())
    Cons(hd, tl) => Cons(hd, tl.rev_concat(other.to_list()))
  }
}

///|
pub fn[A] List1::rev(self : List1[A]) -> List1[A] {
  match self.to_list().rev() {
    Cons(hd, tl) => Cons(hd, tl)
    Nil => abort("should not happen: rev of non-empty list is empty")
  }
}

///|
pub fn[A] List1::take(self : List1[A], n : Int) -> List1[A]? {
  match self.to_list().take(n) {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A] List1::drop(self : List1[A], n : Int) -> List1[A]? {
  match self.to_list().drop(n) {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A : Eq, B] List1::lookup(self : List1[(A, B)], v : A) -> B? {
  self.to_list().lookup(v)
}

///|
pub fn[A] List1::find(self : List1[A], f : (A) -> Bool) -> A? {
  self.to_list().find(f)
}

///|
pub fn[A] List1::iter(self : List1[A]) -> Iter[A] {
  self.to_list().iter()
}

///|
pub fn[A] List1::iter2(self : List1[A]) -> Iter2[Int, A] {
  self.to_list().iter2()
}

///|
pub fn[A] List1::singleton(a : A) -> List1[A] {
  Cons(a, List::Nil)
}

///|
pub impl[A : Hash] Hash for List1[A] with hash_combine(self, h) {
  self.to_list().hash_combine(h)
}

///|
pub impl[A : Show] Show for List1[A] with output(xs, logger) {
  logger.write_iter(xs.iter(), prefix="@list.of([", suffix="])")
}

///|
pub(all) enum List2[A] {
  Cons(A, A, List[A])
} derive(Eq)

///|
pub fn[A, B] List2::map(
  self : List2[A],
  f : (A) -> B raise?,
) -> List2[B] raise? {
  match self {
    Cons(a1, a2, tl) => Cons(f(a1), f(a2), map_exn(tl, f))
  }
}

///|
pub fn[A] List2::to_list(self : List2[A]) -> List[A] {
  match self {
    Cons(a1, a2, tl) => Cons(a1, Cons(a2, tl))
  }
}

///|
pub fn[A] List2::to_array(self : List2[A]) -> Array[A] {
  let arr = []
  match self {
    Cons(a1, a2, tl) => {
      arr.push(a1)
      arr.push(a2)
      loop tl {
        Nil => ()
        Cons(hd, tl) => {
          arr.push(hd)
          continue tl
        }
      }
      arr
    }
  }
}

///|
pub fn[A] List2::iter(self : List2[A]) -> Iter[A] {
  self.to_list().iter()
}
