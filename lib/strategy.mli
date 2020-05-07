open Core

module TropicalNat : sig 
  type t = Inf | Int of int [@@deriving sexp]
  include Comparable.S with type t := t
end


type t

(* val poss_init : t -> State.t -> string -> 'a list
 * 
 * val poss_moves : t -> State.t -> string -> 'a list *)

val solve : Game.t -> int -> t

val calcExtents : Game.t -> int -> Game.bdd Map.M(TropicalNat).t

val acceptStrategy : t -> Game.bdd
val attractor : t -> Game.bdd
val goodForEnergy : t -> Game.bdd
val threshold : t -> Game.bdd Map.M(Int).t
val getExtents : t -> Game.bdd Map.M(TropicalNat).t
