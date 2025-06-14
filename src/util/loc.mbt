///|
pub(all) struct Loc {
  mut line : Int
  mut column : Int
  mut index : Int
} derive(Hash, Eq)

///|
pub(all) enum Range {
  NoRange
  Range(Array[Loc]) // a sequence of consecutive locations
} derive(Show)

///|
pub impl Show for Loc with output(self, logger) {
  logger.write_string(
    "line \{self.line}, column \{self.column}, index \{self.index}",
  )
}

///|
pub fn Loc::to_string(self : Loc) -> String {
  Show::to_string(self)
}

///|
pub fn Range::new(locs : Array[Loc]) -> Range {
  if locs.length() == 0 {
    Range::NoRange
  } else {
    Range::Range(locs)
  }
}
