type t = { env_vars  : var_def list;
           sys_vars  : var_def list;
           env_init  : formula list;
           sys_init  : formula list;
           env_trans : formula list;
           sys_trans : formula list;
           sys_goals : formula list;
           weights   : weight_def list;
         }
[@@deriving show]

and formula =
  | And of (formula * formula)
  | Or of (formula * formula)
  | Not of formula
  | Atom of atom
[@@deriving show]

and atom =
  | Lt of (term * term)
  | Gt of (term * term)
  | Eq of (term * term)
  | Bvar of string
  | Bool of bool
[@@deriving show]

and term =
  | Add of (term * term)
  | Sub of (term * term)
  (* | Mul of (term * term) *)
  (* | Div of (term * term) *)
  (* | IfElse of (atom * term * term) *)
  | Ivar of string
  | Int of int
[@@deriving show]

and weight_def = formula * int [@@deriving show]

and var_def =
  | BoolVarDef of string
  | IntVarDef of string * int * int
[@@deriving show]
