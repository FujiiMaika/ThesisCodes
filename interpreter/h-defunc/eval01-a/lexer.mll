{
open Parser
}

(* Omission of regular expression *)
let space = [' ' '\t' '\n' '\r']
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper

rule token = parse
| space+ { token lexbuf }       (* Skip spaces *)
| "(*" [^ '\n']* "\n"           (* comment from '( *'  *)
         { token lexbuf }
| "("    { LPAREN }
| ")"    { RPAREN }
| "+"    { PLUS }
| "-"    { MINUS }
| "*"    { TIMES }
| "/"    { DIVIDE }
| "="    { EQUAL }
| "<"    { LESS }
| "true" { TRUE }
| "false" { FALSE }
| "fun"  { FUN }
| "->"   { ARROW }
| "if"   { IF }
| "then" { THEN }
| "else" { ELSE }
| "try"  { TRY }
| "with" { WITH }
| ";"    { SEM }
| "call_d" { CALLD }
| "call_s" { CALLS }
| "let"  { LET }
| "rec"  { REC }
| "in"   { IN }
| digit +
         { NUMBER (int_of_string (Lexing.lexeme lexbuf)) }
| lower (alpha | digit) *
         { VAR (Lexing.lexeme lexbuf) }
| eof    { EOF }                (* End of file *)
| _      { failwith ("unknown token: " ^ Lexing.lexeme lexbuf) }
