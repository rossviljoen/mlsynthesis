open Core

type t

(* val poss_init : t -> State.t -> string -> 'a list
 * 
 * val poss_moves : t -> State.t -> string -> 'a list *)

val solve : Game.t -> int -> t

val acceptStrategy : t -> Game.bdd
val attractor : t -> Game.bdd
val goodForEnergy : t -> Game.bdd
val threshold : t -> Game.bdd Map.M(Int).t
