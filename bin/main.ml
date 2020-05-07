open Core
open Lexing
open Synthesis                  (* This project's libraries *)

let rec parse_and_print lexbuf =
  match Utils.parse_with_error lexbuf with
  | Some tree ->
    let game = Game.make_game tree in
    let strat = Strategy.solve game 100 in
    (* printf "%s\n" (Syntax.show tree); *)

    (* Game.pp_bdd game (Map.find_exn (Game.weights game) (0)); *)
    Format.printf "acceptor strat: %a\n" (Cudd.Bdd.print_minterm (Utils.print_id game)) (Strategy.acceptStrategy strat);
    
     Format.printf "%a\n" (Cudd.Bdd.print_minterm (Utils.print_id game))
       (Map.find_exn (Strategy.getExtents strat) (Strategy.TropicalNat.Int 0));

      printf "%s\n" (List.to_string ~f:(fun x -> Sexp.to_string(Strategy.TropicalNat.sexp_of_t x)) (Map.keys (Strategy.getExtents strat)));

      (* Game.pp_bdd game (Game.env_trans game); *)
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

