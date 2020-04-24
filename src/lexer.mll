{
open Lexing
open Parser

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
               pos_lnum = pos.pos_lnum + 1
    }
}

let int = '-'? ['0'-'9'] ['0'-'9']*

let white = [' ' '\t']+
let newline = '\r' | '\n' | "\r\n"
let var = ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '0'-'9' '_' ]*
let var_prime = var '\''

let env_vars    = "[env_vars]"
let sys_vars    = "[sys_vars]"
let env_init    = "[env_init]"
let sys_init    = "[sys_init]"
let env_trans   = "[env_trans]"
let sys_trans   = "[sys_trans]"
let sys_goals   = "[sys_goals]"
let weights     = "[weights]"

rule read =
  parse
  | white     { read lexbuf }
  | newline   { next_line lexbuf; read lexbuf }
  | int       { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | "true"    { TRUE }
  | "false"   { FALSE }
  | var       { VAR (Lexing.lexeme lexbuf) }
  | var_prime { VARPRIME (Lexing.lexeme lexbuf) }
  | '&'       { AND }
  | '|'       { OR }
  | '!'       { NOT }
  | "->"      { IMPL }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | '['       { LBRACK }
  | ']'       { RBRACK }
  | ".."      { ELLIPSIS }
  | '<'       { LT }
  | '>'       { GT } 
  | '='       { EQ }
  | '+'       { ADD }
  | '-'       { SUB }
  (* | '*'       { MUL } *)
  (* | '/'       { DIV } *)
  | ':'       { COLON }
  | eof       { EOF }
  | env_vars  { ENV_VARS }
  | sys_vars  { SYS_VARS }
  | env_init  { ENV_INIT }
  | sys_init  { SYS_INIT }
  | env_trans { ENV_TRANS }
  | sys_trans { SYS_TRANS }
  | sys_goals { SYS_GOALS }
  | weights   { WEIGHTS }
