
type! EndOfInput

typealias Token = @parser.Token

pub fn tokenize(
  input : String
) -> Array[(Token, Int, Int)] {
  let tokens : Array[(Token , Int, Int)] = []
  let end = input.length()
  let mut cursor = 0

  fn peek_char!() {
    guard cursor < end else { raise EndOfInput }
    input[cursor]
  }

  fn advance() {
    cursor += 1
  }

  fn read_token!() -> (Token, Int, Int) {
    let start = cursor
    match peek_char!() {
      '0'..='9' | 'a'..='z' | 'A'..='Z' | '_' | '$' as c => {
        advance()
        let id = read_ident!(c)
        let tk : Token = match c {
          '0'..='9' => NUMBER(@strconv.parse_int!(id))
          _ => match id {
            "Set" => KW_SET
            "let" => KW_LET
            "in" => KW_IN
            "data" => KW_DATA
            "where" => KW_WHERE
            "normalize" => KW_NORM
            "infer" => KW_INFER
            "checkctx" => KW_CHECK
            "mutual" => KW_MUTUAL
            "end" => KW_END
            _ => IDENT(id)
          }
        } 
        (tk, start, cursor)
      }
      '(' => {
        advance()
        (LPAREN, start, cursor)
      }
      ')' => {
        advance()
        (RPAREN, start, cursor)
      }
      '[' => { advance(); (LREC, start, cursor) }   
      ']' => { advance(); (RREC, start, cursor) }     
      '{' => { advance(); (LCURLY, start, cursor) }   
      '}' => { advance(); (RCURLY, start, cursor) }  
      '\n' => { advance(); (NEWLINE, start, cursor) }     
      '|' => { advance(); (BAR, start, cursor) }      
      ':' => { 
        advance()
        let b = peek_char!()
        if b == ':' {
          advance()
          let c = peek_char!()
          if c == '=' {
            advance()
            (DEFN, start, cursor)
          }else{
            panic()
          }
        }else{
          (COLON, start, cursor)
        }
      }    
      '.' => { advance(); (DOT, start, cursor) }    
      '\\' => { advance(); (LAMBDA, start, cursor) }  
      '=' => { advance(); (EQ, start, cursor) }      
      '?' => { advance(); (QM, start, cursor) }  
      '-' => { 
        advance()
        let a = peek_char!()
        advance()
        if a == '>' {
          (ARROW, start, cursor)
        } else {
          let b = peek_char!()
          advance()
          if a == '-' && b == ':' {
            (CMD, start, cursor)
          } else {
            panic()
          }
        }
      }

      ' ' | '\t' | '\r'  => {
        advance()
        read_token!()
      }
      _ as c => {
        println("Error: Unidentified Symbol " + [c])
        panic()
      }
    }
  }

  fn read_ident!(first_char : Char) -> String{
    let buf = StringBuilder::new()
    buf.write_char(first_char)
    while true {
      match peek_char?() {
        Ok('0'..='9' | 'a'..='z' | 'A'..='Z' | '_' | '$' as c) => {
          buf.write_char(c)
          advance()
        }
        Ok(_) | Err(EndOfInput) => break
        Err(err) => raise err
      }
    }
    buf.to_string()
  }

  while true {
    // println(cursor)
    try {
      read_token!()
    } catch {
      EndOfInput => break
      _ => panic()
    } else {
      token => tokens.push(token)
    }
  }
  tokens.push((EOF, cursor, cursor))
  tokens
}