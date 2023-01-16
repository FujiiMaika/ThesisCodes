(* main *)
let go () =
  let program = Parser.expr Lexer.token (Lexing.from_channel stdin) in
  if Array.length Sys.argv = 1 then begin
    print_string "Parsed : ";
    Syntax.print program;               (* input *)
    print_newline ();
    print_string "Result : "
  end;
  Value.print (Eval.f program) ;(* result *)
  print_newline ()

(* startup *)
let _ = go ()
