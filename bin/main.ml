open Core
open Lexing
open Synthesis                  (* This project's libraries *)
open Lexer

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

let print_id game fmt id = Format.pp_print_string fmt (Map.find_exn (Game.var_names game) id)

let rec parse_and_print lexbuf =
  match parse_with_error lexbuf with
  | Some tree ->
    let game = Game.make_game tree in
    let strat = Strategy.solve game 50 in
    (* printf "%s\n" (Syntax.show value); *)

    (* Format.printf "%a" (Cudd.Bdd.print (print_id game)) (Game.env_init game); *)
    Format.printf "%a" (Cudd.Bdd.print_minterm (print_id game)) (Strategy.attractor strat);
    
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


let parse_tree_from_file filename =
  let inx = In_channel.create filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  match parse_with_error lexbuf with
  | Some tree -> tree
  | None -> assert false
          
