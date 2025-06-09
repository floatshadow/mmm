///|
typealias MutMap = @hashmap.T[String, Keyword]

///|

///|
typealias @util.Loc

///|
priv type! InvalidCharcode (Int, Loc)

///|
pub struct Lexer {
  buffer : String
  flags : Array[Array[Token]]
  mut index : Int
  mut colstart : Int
  mut line : Int
} derive(Show)

///|
pub enum Keyword {
  Let
  Where
  Data
  Postulate
} derive(Hash, Eq, Show)

///|
pub enum Paired {
  Parenthesis
  Bracket
  Brace
} derive(Hash, Eq, Show)

///|
pub enum TokenTag {
  Eof
  Newline
  Identifer
  Kw(Keyword)
  IntLiteral(Int)
  Op(String)
  PairedOpen(Paired)
  PairedClose(Paired)
  Error(String)
} derive(Hash, Eq, Show)

///|
let keywords : MutMap = @hashmap.new()

///|
fn init {
  keywords["let"] = Keyword::Let
  keywords["where"] = Keyword::Where
  keywords["data"] = Keyword::Data
  keywords["postulate"] = Keyword::Postulate
}

///|
pub(all) struct Token {
  tag : TokenTag
  loc : Loc
  span : String
} derive(Hash, Eq, Show)

///|
fn Token::new(tag : TokenTag, loc : Loc, span : String) -> Token {
  { tag, loc, span }
}

///|
pub fn Lexer::new(s : String) -> Lexer {
  let buffer = StringBuilder::new(size_hint=s.length() + 1)
  buffer.write_string(s)
  buffer.write_char(Int::unsafe_to_char(0))
  Lexer::{
    buffer: buffer.to_string(),
    flags: [],
    index: 0,
    colstart: 0,
    line: 1,
  }
}

///|
pub fn Lexer::reset(self : Lexer) -> Unit {
  self.index = 0
  self.colstart = 0
  self.line = 1
}

///|
fn Lexer::move_to_newline(self : Lexer) -> Unit {
  self.colstart = self.index
  self.line += 1
}

///|
fn Lexer::get_loc(self : Lexer) -> Loc {
  { line: self.line, column: self.index - self.colstart + 1, index: self.index }
}

///|
fn Lexer::make_span(self : Lexer, start : Int) -> String {
  self.buffer.substring(start~, end=self.index)
}

///|
fn Lexer::make_token(self : Lexer, tag : TokenTag, loc : Loc) -> Token {
  Token::new(tag, loc, self.make_span(loc.index))
}

///|
fn Lexer::make_error(self : Lexer, loc : Loc, msg : String) -> Token {
  Token::new(TokenTag::Error(msg), loc, self.make_span(loc.index))
}

///|
fn Lexer::eof(self : Lexer) -> Token {
  Token::new(TokenTag::Eof, self.get_loc(), "<empty>")
}

///|
fn Lexer::is_keyword(s : String) -> Keyword? {
  keywords.get(s)
}

///|
fn Lexer::ch(self : Lexer) -> Char!InvalidCharcode {
  let charcode = self.buffer.charcode_at(self.index)
  match Int::to_char(charcode) {
    Some(c) => c
    None => raise InvalidCharcode((charcode, self.get_loc()))
  }
}

///|
fn Lexer::ch_at(self : Lexer, i : Int) -> Char!InvalidCharcode {
  let charcode = self.buffer.charcode_at(self.index + i)
  match Int::to_char(charcode) {
    Some(c) => c
    None => raise InvalidCharcode((charcode, self.get_loc()))
  }
}

///|
fn Lexer::numeric_literal(self : Lexer, loc : Loc) -> Token!InvalidCharcode {
  let start = self.index
  self.index += 1
  while true {
    let n = self.ch!()
    if n < '0' || n > '9' {
      break
    }
    self.index += 1
  }
  try {
    let value = @strconv.parse_int!(
      self.buffer.substring(start~, end=self.index),
    )
    self.make_token(TokenTag::IntLiteral(value), loc)
  } catch {
    StrConvError(msg) => self.make_error(loc, msg)
  }
}

///|
fn Lexer::ident(self : Lexer, loc : Loc) -> Token!InvalidCharcode {
  while true {
    let cond = (self.ch() >= 'a' && self.ch() <= 'z') ||
      (self.ch() >= 'A' && self.ch() <= 'Z') ||
      self.ch() == '_' ||
      (self.ch() >= '0' && self.ch() <= '9')
    if not(cond) {
      break
    }
    self.index += 1
  }
  let tok = self.make_token(TokenTag::Identifer, loc)
  Lexer::is_keyword(tok.span).map_or(tok, fn(kw) {
    Token::new(TokenTag::Kw(kw), loc, tok.span)
  })
}

///|
fn Lexer::flag(self : Lexer) -> Array[Array[Token]]!InvalidCharcode {
  let res = []
  let flag = []
  while true {
    let ident = self.ident(self.get_loc())
    let arg = match ident.tag {
      TokenTag::Identifer => ident
      _ => self.make_error(ident.loc, "invalid flag \{ident.span}")
    }
    flag.push(arg)
    self.skip_inline_whitespace()
    if self.ch() == '\n' || self.ch() == '\u{00}' {
      res.push(flag.copy())
      flag.clear()
      break
    }
    self.index += 1
  }
  res
}

///|
fn Lexer::skip_inline_whitespace(self : Lexer) -> Unit!InvalidCharcode {
  while true {
    let c = self.ch()
    if c == '\u{00}' || c == '\n' {
      break
    } else if c == ' ' || c == '\t' || c == '\r' {
      self.index += 1
      continue
    } else {
      break
    }
  }
}

///|
fn Lexer::skip_comment(self : Lexer) -> Unit!InvalidCharcode {
  self.index += 2
  let mut has_flag = false
  while true {
    if self.ch() == '\u{00}' {
      break
    } else if self.ch() == '\n' {
      self.index += 1
      self.move_to_newline()
      break
    } else if self.ch() == ':' && not(has_flag) {
      self.index += 1
      has_flag = true
      self.flag().each(fn(f) { self.flags.push(f) })
      continue
    }
    self.index += 1
  }
}

///|
fn Lexer::operator(
  self : Lexer,
  loc : Loc,
  first_c : Char
) -> Token!InvalidCharcode {
  self.index += 1
  let buf = StringBuilder::new()
  buf.write_char(first_c)
  match first_c {
    // reserve single-character operator
    ':' | ';' | '.' | '|' =>
      return self.make_token(TokenTag::Op(buf.to_string()), loc)
    '*' | '+' | '-' | '/' | '\\' | '=' | '>' | '<' | '^' | '%' =>
      loop self.ch() {
        '*' | '+' | '-' | '/' | '\\' | '=' | '>' | '<' | '^' | '%' => {
          buf.write_char(self.ch())
          self.index += 1
          continue self.ch()
        }
        _ => break
      }
    _ => return self.make_error(loc, "invalid operator")
  }
  self.make_token(TokenTag::Op(buf.to_string()), loc)
}

///|
pub fn Lexer::next_err(self : Lexer) -> Token!Failure {
  let tok = self.next()
  match tok.tag {
    TokenTag::Error(msg) => fail!(msg)
    _ => tok
  }
}

///|
fn Lexer::next(self : Lexer) -> Token {
  try {
    while true {
      let c = self.ch()
      let loc = self.get_loc()
      match c {
        '\u{00}' => return self.eof()
        ' ' | '\t' | '\r' => {
          self.skip_inline_whitespace()
          continue
        }
        '\n' => {
          self.index += 1
          self.move_to_newline()
          return self.make_token(TokenTag::Newline, loc)
        }
        '(' => {
          self.index += 1
          return self.make_token(TokenTag::PairedOpen(Paired::Parenthesis), loc)
        }
        ')' => {
          self.index += 1
          return self.make_token(
            TokenTag::PairedClose(Paired::Parenthesis),
            loc,
          )
        }
        '[' => {
          self.index += 1
          return self.make_token(TokenTag::PairedOpen(Paired::Bracket), loc)
        }
        ']' => {
          self.index += 1
          return self.make_token(TokenTag::PairedClose(Paired::Bracket), loc)
        }
        '{' => {
          self.index += 1
          return self.make_token(TokenTag::PairedOpen(Paired::Brace), loc)
        }
        '}' => {
          self.index += 1
          return self.make_token(TokenTag::PairedClose(Paired::Brace), loc)
        }
        '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' =>
          return self.numeric_literal(loc)
        '-' =>
          if self.ch_at(1) == '-' {
            self.skip_comment()
            continue
          } else {
            return self.operator(loc, c)
          }
        '+'
        | ','
        | ';'
        | ':'
        | '.'
        | '*'
        | '/'
        | '\\'
        | '='
        | '>'
        | '<'
        | '^'
        | '|'
        | '%' => return self.operator(loc, c)
        _ =>
          if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' {
            return self.ident(loc)
          } else {
            return self.make_error(loc, "invalid character: \{c}")
          }
      }
    } else {
      return self.make_error(self.get_loc(), "unreachable")
    }
  } catch {
    InvalidCharcode((charcode, loc)) =>
      self.make_error(loc, "invalid character code: \{charcode}")
  }
}
