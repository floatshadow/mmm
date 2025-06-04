struct Options {
  mut file: String?
  mut debug: Bool
}

fn Options::new() -> Options {
  Options:: { file: None, debug: false }
}

let opts: Options = Options::new()

fn main {
  let argv = @sys.get_cli_args()
  // moonrun *.wasm [args...]
  let truncated_argv = argv.split_at(1).1
  @ArgParser.parse(
    [("--debug", "", @ArgParser.Unit(fn() {opts.debug = true}), "Debug mode" ) ],
    fn(s) {
      if opts.file.is_empty() {
        opts.file = Some(s)
      } else {
        abort("multiple files given")
      }
    },
    "",
    truncated_argv
  )

  let file = match opts.file {
    Some(f) => f
    None => abort("no input file given")
  }

  try {
    let contents = @fs.read_file_to_string!(file)
    let lexer = @lexer.Lexer::new(contents)
    println("Lexer initialized with file: \{contents}")
    while true {
      match lexer.next_err!() {
        { tag: @lexer.TokenTag::Eof, .. } => break
        _ as tok => println("\{tok}")
      }
    }
  } catch {
    Failure(msg) => println("\{msg}")
    _ as err => println("\{err}")
  }
}