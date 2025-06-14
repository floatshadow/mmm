///|
typealias @immut/list.T as List

///|
typealias NonEmptyList as T

///|
pub(all) enum NonEmptyList[A] {
  Cons(A, List[A])
} derive(Eq)

///| Extract the first element of the non-empty list.
pub fn[A] T::head(self : T[A]) -> A {
  match self {
    Cons(hd, _) => hd
  }
}

///| Extract the possibly-empty tail of the non-empty list.
pub fn[A] T::tail(self : T[A]) -> List[A] {
  match self {
    Cons(_, tl) => tl
  }
}

///|
pub fn[A] T::cons(self : T[A], value : A) -> T[A] {
  match self {
    Cons(hd, tl) => Cons(value, Cons(hd, tl))
  }
}

///|
/// Get the length of the list.
pub fn[A] T::length(self : T[A]) -> Int {
  match self {
    Cons(_, tl) => 1 + tl.length()
  }
}

///|
pub fn[A, B] T::map(self : T[A], f : (A) -> B) -> T[B] {
  match self {
    Cons(hd, tl) => Cons(f(hd), tl.map(f))
  }
}

///|
pub fn[A] T::each(self : T[A], f : (A) -> Unit) -> Unit {
  match self {
    Cons(hd, tl) => {
      f(hd)
      tl.each(f)
    }
  }
}

///|
pub fn[A] T::all(self : T[A], f : (A) -> Bool) -> Bool {
  match self {
    Cons(hd, tl) => if f(hd) { tl.all(f) } else { false }
  }
}

///|
pub fn[A] T::any(self : T[A], f : (A) -> Bool) -> Bool {
  match self {
    Cons(hd, tl) => f(hd) || tl.any(f)
  }
}

///|
pub fn[A, B] T::fold(self : T[A], init~ : B, f : (B, A) -> B) -> B {
  match self {
    Cons(hd, tl) => tl.fold(init=f(init, hd), f)
  }
}

///|
pub fn[A] T::from_list(xs : List[A]) -> T[A]? {
  match xs {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A] T::from_array(arr : Array[A]) -> T[A]? {
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
pub fn[A] T::to_list(self : T[A]) -> List[A] {
  match self {
    Cons(hd, tl) => Cons(hd, tl)
  }
}

///|
pub fn[A] T::to_array(self : T[A]) -> Array[A] {
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
pub fn[A] T::concat(self : T[A], other : T[A]) -> T[A] {
  match self {
    Cons(hd, tl) => Cons(hd, tl.concat(other.to_list()))
  }
}

///|
pub fn[A] T::rev_concat(self : T[A], other : T[A]) -> T[A] {
  match self {
    Cons(hd, Nil) => Cons(hd, other.to_list())
    Cons(hd, tl) => Cons(hd, tl.rev_concat(other.to_list()))
  }
}

///|
pub fn[A] T::rev(self : T[A]) -> T[A] {
  match self.to_list().rev() {
    Cons(hd, tl) => Cons(hd, tl)
    Nil => abort("should not happen: rev of non-empty list is empty")
  }
}

///|
pub fn[A] T::take(self : T[A], n : Int) -> T[A]? {
  match self.to_list().take(n) {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A] T::drop(self : T[A], n : Int) -> T[A]? {
  match self.to_list().drop(n) {
    Nil => None
    Cons(hd, tl) => Some(Cons(hd, tl))
  }
}

///|
pub fn[A : Eq, B] T::lookup(self : T[(A, B)], v : A) -> B? {
  self.to_list().lookup(v)
}

///|
pub fn[A] T::find(self : T[A], f : (A) -> Bool) -> A? {
  self.to_list().find(f)
}

///|
pub fn[A] T::iter(self : T[A]) -> Iter[A] {
  self.to_list().iter()
}

///|
pub fn[A] T::iter2(self : T[A]) -> Iter2[Int, A] {
  self.to_list().iter2()
}

///|
pub fn[A] T::singleton(a : A) -> T[A] {
  Cons(a, List::Nil)
}

///|
pub impl[A : Hash] Hash for T[A] with hash_combine(self, h) {
  self.to_list().hash_combine(h)
}

///|
pub impl[A : Show] Show for T[A] with output(xs, logger) {
  logger.write_iter(xs.iter(), prefix="@list.of([", suffix="])")
}
