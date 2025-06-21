///|
typealias @hashmap.T[String, Keyword] as MutMap

///|
typealias @queue.T as Queue

///|
typealias @util.NonEmptyList as List1

///|
typealias @util.Loc

typealias @util.Interval

///|
priv suberror InvalidCharcode (Int, Loc)

///|
pub struct Lexer {
  buffer : String
  mut indents : List1[Int]
  tokenbuf : Queue[Token]
  mut index : Int
  mut colstart : Int
  mut line : Int
} derive(Show)

///|
pub enum Keyword {
  Set
  Where
  Data
  Postulate
  Mutual
  CheckCtx
  InferType
  Normalize
} derive(Hash, Eq, Show)

typealias @parser.Token
///|
let keywords : MutMap = @hashmap.new()

///|
fn init {
  keywords["Set"] = Keyword::Set
  keywords["where"] = Keyword::Where
  keywords["data"] = Keyword::Data
  keywords["postulate"] = Keyword::Postulate
  keywords["mutual"] = Keyword::Mutual
  keywords["CHECKCTX"] = Keyword::CheckCtx
  keywords["INFER"] = Keyword::InferType
  keywords["NORM"] = Keyword::Normalize
}

///|
pub fn Lexer::new(s : String) -> Lexer {
  let buffer = StringBuilder::new(size_hint=s.length() + 1)
  buffer.write_string(s)
  buffer.write_char(Int::unsafe_to_char(0))
  Lexer::{
    buffer: buffer.to_string(),
    indents: List1::singleton(0),
    tokenbuf: @queue.new(),
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

fn Lexer::make_span(self : Lexer, start : Loc) -> String {
  self.buffer.substring(start=start.index, end=self.index)
}


///|
fn Lexer::make_error(loc : Loc, msg : String) -> Token {
  Token::ErrorMsg((loc, msg))
}

///|
fn Lexer::eof() -> Token {
  Token::Eof
}

///|
fn Lexer::is_keyword(s : String) -> Keyword? {
  keywords.get(s)
}

///|
fn Lexer::ch(self : Lexer) -> Char raise InvalidCharcode {
  let charcode = self.buffer.charcode_at(self.index)
  match Int::to_char(charcode) {
    Some(c) => c
    None => raise InvalidCharcode((charcode, self.get_loc()))
  }
}

///|
fn Lexer::ch_at(self : Lexer, i : Int) -> Char raise InvalidCharcode {
  let charcode = self.buffer.charcode_at(self.index + i)
  match Int::to_char(charcode) {
    Some(c) => c
    None => raise InvalidCharcode((charcode, self.get_loc()))
  }
}

///|
fn Lexer::numeric_literal(
  self : Lexer,
  begin : Loc
) -> Token raise InvalidCharcode {
  let start = self.index
  self.index += 1
  while true {
    let n = self.ch()
    if n < '0' || n > '9' {
      break
    }
    self.index += 1
  }
  try {
    let value = @strconv.parse_int(
      self.buffer.substring(start~, end=self.index),
    )
    let end = self.get_loc()
    Token::IntLiteral((Interval::new(begin, end), value))
  } catch {
    StrConvError(msg) => Lexer::make_error(begin, msg)
  }
}

///|
fn Lexer::ident(self : Lexer, begin : Loc) -> Token raise InvalidCharcode {
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
  let end = self.get_loc()
  let interval = Interval::new(begin, end)
  let span = self.make_span(begin)
  let tok = Token::Id((interval, span))
  Lexer::is_keyword(span).map_or(tok, fn(kw) {
    match kw {
      Keyword::Set => Token::KwSet(interval)
      Keyword::Where => Token::KwWhere(interval)
      Keyword::Data => Token::KwData(interval)
      Keyword::Postulate => Token::KwPostulate(interval)
      Keyword::Mutual => Token::KwMutual(interval)
      Keyword::CheckCtx => Token::KwCheck(interval)
      Keyword::InferType => Token::KwInfer(interval)
      Keyword::Normalize => Token::KwNorm(interval)
    }
  })
}

///|
fn Lexer::command(self : Lexer) -> Array[Array[Token]] raise InvalidCharcode {
  let res = []
  let flag = []
  while true {
    let begin = self.get_loc()
    let ident = self.ident(begin)
    let arg = match ident {
      Token::Id(_) | Token::KwCheck(_) | Token::KwInfer(_) | Token::KwNorm(_) => ident
      _ => Lexer::make_error(begin, "invalid command argument \{ident}")
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
fn Lexer::skip_inline_whitespace(self : Lexer) -> Unit raise InvalidCharcode {
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
fn Lexer::skip_comment(self : Lexer) -> Unit raise InvalidCharcode {
  self.index += 2
  let mut has_cmd = false
  while true {
    if self.ch() == '\u{00}' {
      break
    } else if self.ch() == '\n' {
      self.index += 1
      self.move_to_newline()
      break
    } else if self.ch() == ':' && not(has_cmd) {
      self.index += 1
      has_cmd = true
      let cmds = self.command()
      for cmd in cmds {
        self.push_tokens(cmd)
      }
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
) -> Token raise InvalidCharcode {
  self.index += 1
  match first_c {
    // reserve single-character operator
    ':' => Token::SymColon(Interval::new(loc, loc))
    '.' => Token::SymDot(Interval::new(loc, loc))
    '=' => Token::SymEqual(Interval::new(loc, loc))
    '_' => Token::SymUnderscore(Interval::new(loc, loc))
    '(' => Token::SymOpenParen(Interval::new(loc, loc))
    ')' => Token::SymCloseParen(Interval::new(loc, loc))
    '{' => Token::SymOpenBrace(Interval::new(loc, loc))
    '}' => Token::SymCloseBrace(Interval::new(loc, loc))
    '\\' => Token::SymLambda(Interval::new(loc, loc))
    '-' if self.ch() == '>' => {
          self.index += 1
          Token::SymArrow(Interval::new(loc, self.get_loc()))
      }
    _ => Lexer::make_error(loc, "invalid operator")
  }
}

///|
pub fn Lexer::next_err(self : Lexer) -> Token raise Failure {
  match self.tokenbuf.pop() {
    Some(tok) =>
      match tok {
        ErrorMsg((_, msg)) => fail(msg)
        _ => tok
      }
    None => {
      self.lex()
      self.next_err()
    }
  }
}

///|
fn Lexer::push_token(self : Lexer, tok : Token) -> Unit {
  self.tokenbuf.push(tok)
}

fn Lexer::push_tokens(self : Lexer, toks : Array[Token]) -> Unit {
  for tok in toks {
    self.push_token(tok)
  }
}

///| Following Python, leading whitespace (spaces and tabs) at the beginning 
/// of a logical line is used to compute the indentation level of the line. 
fn Lexer::indent_level(self : Lexer, loc : Loc) -> Int? raise InvalidCharcode {
  if loc.column != 1 {
    return None
  }
  let mut indent = 0
  while true {
    let c = self.ch()
    // empty line or end of file: this line itself is not a logical line.
    if c == '\u{00}' || c == '\n' {
      return None
    } else if c == ' ' || c == '\t' || c == '\r' {
      self.index += 1
      indent += 1
      continue
    } else if c == '-' && self.ch_at(1) == '-' {
      // handling comments
      return None
    } else {
      break
    }
  }
  Some(indent)
}

///| Given the new indent level, generate appropriate INDENT or OUTDENT token(s).
fn Lexer::indent(self : Lexer, indent : Int) -> Unit {
  let top_level = self.indents.head()
  if indent == top_level {
    // nothing happens
    return
  } else if indent > top_level {
    self.push_token(
      Token::Indent,
    )
    self.indents = self.indents.cons(indent)
  } else if indent < top_level {
    let mut top_level = top_level
    while indent < top_level {
      self.push_token(
        Token::Outdent
      )
      self.indents = self.indents.drop(1).unwrap()
      top_level = self.indents.head()
    }
  }
}

///|
fn Lexer::lex(self : Lexer) -> Unit {
  try {
    while true {
      let c = self.ch()
      let loc = self.get_loc()
      if self.indent_level(loc) is Some(indent) {
        self.indent(indent)
      }
      match c {
        '\u{00}' => {
          self.indent(0)
          self.push_token(Lexer::eof())
          break
        }
        ' ' | '\t' | '\r' => {
          self.skip_inline_whitespace()
          continue
        }
        '\n' => {
          self.index += 1
          self.move_to_newline()
          self.push_token(Token::Newline(loc))
          break
        }
        '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => {
          self.push_token(self.numeric_literal(loc))
          break
        }
        '-' =>
          if self.ch_at(1) == '-' {
            self.skip_comment()
            continue
          } else {
            self.push_token(self.operator(loc, c))
            break
          }
        ':' | '=' | '.' | '(' | ')' | '{' | '}' | '\\' => {
          self.push_token(self.operator(loc, c))
          break
        }
        _ =>
          if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_' {
            self.push_token(self.ident(loc))
            break
          } else {
            self.push_token(Lexer::make_error(loc, "invalid character: \{c}"))
            break
          }
      }
    }
  } catch {
    InvalidCharcode((charcode, loc)) =>
      self.push_token(
        Lexer::make_error(loc, "invalid character code: \{charcode}"),
      )
  }
}
