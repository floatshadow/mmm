///|
typealias @hashmap.T[String, Keyword] as MutMap

///|
typealias @queue.T as Queue

///|
typealias @util.List1

///|
typealias @util.Loc

///|
typealias @util.Interval

///|
priv suberror InvalidCharcode (Int, Loc)

///|
pub struct Lexer {
  buffer : String
  mut indents : List1[Int]
  tokenbuf : Queue[(Token, Interval)]
  mut last_token : Token?
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

///|
typealias @parser.Token

/// See https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Parser/Layout.hs
/// to allow stacking of layout keywords on the same line.

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
    last_token: None,
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
fn Lexer::make_span(self : Lexer, start : Loc) -> String {
  self.buffer.substring(start=start.index, end=self.index)
}

///|
fn Lexer::make_error(loc : Loc, msg : String) -> (Token, Interval) {
  (Token::ErrorMsg((loc, msg)), Interval::new(loc, loc))
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
) -> (Token, Interval) raise InvalidCharcode {
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
    let interval = Interval::new(begin, end)
    (Token::IntLiteral((interval, value)), interval)
  } catch {
    StrConvError(msg) => Lexer::make_error(begin, msg)
  }
}

///|
fn Lexer::ident(
  self : Lexer,
  begin : Loc
) -> (Token, Interval) raise InvalidCharcode {
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
  let idkw = Lexer::is_keyword(span).map_or(tok, fn(kw) {
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
  (idkw, interval)
}

///|
fn Lexer::command(
  self : Lexer
) -> Array[Array[(Token, Interval)]] raise InvalidCharcode {
  let res = []
  let cmd = []
  while true {
    let begin = self.get_loc()
    let (ident, interval) = self.ident(begin)
    let arg = match ident {
      Token::Id(_) | Token::KwCheck(_) | Token::KwInfer(_) | Token::KwNorm(_) =>
        (ident, interval)
      _ => Lexer::make_error(begin, "invalid command argument \{ident}")
    }
    cmd.push(arg)
    self.skip_inline_whitespace()
    if self.ch() == '\n' || self.ch() == '\u{00}' {
      res.push(cmd.copy())
      cmd.clear()
      break
    }
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
  let loc = self.get_loc()
  self.index += 2
  let mut has_cmd = false
  while true {
    if self.ch() == '\u{00}' {
      break
    } else if self.ch() == '\n' {
      break
    } else if self.ch() == ':' && not(has_cmd) {
      self.index += 1
      has_cmd = true
      let cmds = self.command()
      self.push_token((Token::VSemi, Interval::new(loc, loc)))
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
) -> (Token, Interval) raise InvalidCharcode {
  self.index += 1
  match first_c {
    // reserve single-character operator
    ':' => (Token::SymColon(Interval::new(loc, loc)), Interval::new(loc, loc))
    '.' => (Token::SymDot(Interval::new(loc, loc)), Interval::new(loc, loc))
    '=' => (Token::SymEqual(Interval::new(loc, loc)), Interval::new(loc, loc))
    '_' =>
      (Token::SymUnderscore(Interval::new(loc, loc)), Interval::new(loc, loc))
    '(' =>
      (Token::SymOpenParen(Interval::new(loc, loc)), Interval::new(loc, loc))
    ')' =>
      (Token::SymCloseParen(Interval::new(loc, loc)), Interval::new(loc, loc))
    '{' =>
      (Token::SymOpenBrace(Interval::new(loc, loc)), Interval::new(loc, loc))
    '}' =>
      (Token::SymCloseBrace(Interval::new(loc, loc)), Interval::new(loc, loc))
    '\\' => (Token::SymLambda(Interval::new(loc, loc)), Interval::new(loc, loc))
    '-' if self.ch() == '>' => {
      self.index += 1
      (
        Token::SymArrow(Interval::new(loc, self.get_loc())),
        Interval::new(loc, loc),
      )
    }
    _ => Lexer::make_error(loc, "invalid operator")
  }
}

///|
pub fn Lexer::next_err(self : Lexer) -> (Token, Interval) raise Failure {
  match self.tokenbuf.pop() {
    Some((tok, _) as spaned_token) =>
      match tok {
        ErrorMsg((_, msg)) => fail(msg)
        _ => spaned_token
      }
    None => {
      self.lex()
      self.next_err()
    }
  }
}

///|
fn Lexer::push_token(self : Lexer, tok : (Token, Interval)) -> Unit {
  self.tokenbuf.push(tok)
  self.last_token = Some(tok.0)
}

///|
fn Lexer::push_tokens(self : Lexer, toks : Array[(Token, Interval)]) -> Unit {
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

///|
fn Lexer::offside(self : Lexer, bol : Loc, indent : Int) -> Unit {
  let top_level = self.indents.head()
  let eoi = self.get_loc()
  if indent == top_level {
    // no change in indentation level, produce virtual semicolon
    self.push_token((Token::VSemi, Interval::new(bol, eoi)))
    return
  } else if indent > top_level {
    self.indents = self.indents.cons(indent)
  } else if indent < top_level {
    let mut top_level = top_level
    while indent < top_level {
      self.push_token((Token::VClose, Interval::new(bol, eoi)))
      self.indents = self.indents.drop(1).unwrap()
      top_level = self.indents.head()
    }
    if indent == top_level {
      self.push_token((Token::VSemi, Interval::new(bol, eoi)))
    } else {
      self.push_token(
        Lexer::make_error(
          bol,
          "indentation error: expected \{top_level} bu got \{indent}",
        ),
      )
    }
  }
}

///|
fn Lexer::peek_last_token(self : Lexer) -> Token? {
  self.last_token
}

///|
fn Lexer::is_layout_keyword(self : Lexer, tok : Token) -> Bool {
  match tok {
    Token::KwWhere(_) | Token::KwPostulate(_) | Token::KwMutual(_) => true
    _ => false
  }
}

///|
fn Lexer::lex(self : Lexer) -> Unit {
  try {
    while true {
      let c = self.ch()
      let loc = self.get_loc()
      match c {
        '\u{00}' => {
          let loc = self.get_loc()
          let mut top_level = self.indents.head()
          while 0 < top_level {
            self.push_token((Token::VClose, Interval::new(loc, loc)))
            self.indents = self.indents.drop(1).unwrap()
            top_level = self.indents.head()
          }
          self.push_token((Lexer::eof(), Interval::new(loc, loc)))
          break
        }
        ' ' | '\t' | '\r' => {
          self.skip_inline_whitespace()
          continue
        }
        '\n' => {
          self.index += 1
          self.move_to_newline()
          match self.peek_last_token() {
            Some(tok) if self.is_layout_keyword(tok) => {
              let bol = self.get_loc()
              if self.indent_level(bol) is Some(indent) {
                let eoi = self.get_loc()
                self.push_token((Token::VOpen, Interval::new(bol, eoi)))
                if indent <= self.indents.head() {
                  // empty layout
                  self.push_token((Token::VClose, Interval::new(bol, eoi)))
                } else {
                  self.offside(bol, indent)
                }
              }
            }
            _ => {
              // offside rules
              let bol = self.get_loc()
              if self.indent_level(bol) is Some(indent) {
                self.offside(bol, indent)
              }
            }
          }
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
        ':' | '=' | '.' | '_' | '(' | ')' | '{' | '}' | '\\' => {
          self.push_token(self.operator(loc, c))
          break
        }
        _ =>
          if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') {
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
