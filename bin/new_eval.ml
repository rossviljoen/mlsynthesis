open Core
open Synthesis

let time f =
  let t = Unix.gettimeofday () in
  let res = f () in
  printf "%f\n%!"
                (Unix.gettimeofday () -. t);
  res

let run_bench () =
  Sys.command_exn "rm -f ./evaluation/new/generated_specs/*";
  Sys.command_exn "./evaluation/new/gen.sh";

  let run size = 
    let filename = "./evaluation/new/generated_specs/lift_"^ string_of_int size in
    let inx = In_channel.create filename in
    let lexbuf = Lexing.from_channel inx in
    match Utils.parse_with_error lexbuf with
    | Some tree -> 
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
      let game = Game.make_game tree in
      printf "%d, " size;
      time (fun () -> ignore(Strategy.calcExtents game 100));
      In_channel.close inx;
    | None -> assert false
  in
  List.range ~stride:5 ~stop:`inclusive 5 50
  |> List.iter ~f:(fun n -> run n)

(* let loop filename () =
 *   let inx = In_channel.create filename in
 *   let lexbuf = Lexing.from_channel inx in
 *   lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
 *   regen_specs (); *)
  
  
let () =
  Command.basic_spec ~summary:"Parse and display my super special language"
    Command.Spec.(empty)
    run_bench
  |> Command.run
