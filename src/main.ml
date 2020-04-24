open Core
open Lexer
open Lexing
open Game

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.file Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some value ->
    printf "%s\n" (Syntax.show value);
    parse_and_print lexbuf
  | None -> ()

let loop filename () =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  parse_and_print lexbuf;
  In_channel.close inx

let () =
  Command.basic_spec ~summary:"Parse and display my super special language"
    Command.Spec.(empty +> anon ("filename" %: string))
    loop
  |> Command.run


(* let compile_ops = function
 *   | Rawgame.(Atom (Gt (t, u))) -> Rawgame.(Not (Or (Atom (Lt (t, u)), Atom (Eq (t, u)))))
 *   | f -> f *)
    
(* let first_pass raw_spec =
 *   let g = List.map ~f:compile_ops in
 *   { raw_spec with env_init = g raw_spec.env_init;
 *                   sys_init = g raw_spec.sys_init;
 *                   env_trans = g raw_spec.env_trans;
 *                   sys_trans = g raw_spec.sys_trans;
 *                   sys_goals = g raw_spec.sys_goals;
 *   } *)


