type t

(* val poss_init : t -> State.t -> string -> 'a list
 * 
 * val poss_moves : t -> State.t -> string -> 'a list *)

val solve : Game.t -> int -> t
