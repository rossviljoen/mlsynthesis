open Core

type t

type bdd = Cudd.Bdd.dt

val make_game : Syntax.t -> t

val env_init : t -> bdd
val sys_init : t -> bdd
val env_trans : t -> bdd
val sys_trans : t -> bdd
val sys_goals : t -> bdd
val prime : bdd -> bdd
val env_vars_pr : t -> bdd
val sys_vars_pr : t -> bdd
val weights : t -> bdd Map.M(Int).t
val zero : t -> bdd

val man : t -> Cudd.Man.dt
