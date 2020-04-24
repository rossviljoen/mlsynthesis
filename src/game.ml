open Core

type t = { man : Cudd.Man.dt;
           env_init : bdd;
           sys_init : bdd;
           env_trans : bdd;
           sys_trans : bdd;
           sys_goals : bdd;
           env_vars_primed : bdd;
           sys_vars_primed : bdd;
         }

and bdd = Cudd.Bdd.dt

let zero g = Cudd.Bdd.dtrue g.man
let env_init g = g.env_init
let sys_init g = g.sys_init
let env_trans g = g.env_trans
let sys_trans g = g.sys_trans
let sys_goals g = g.sys_goals
let env_vars_pr g = g.env_vars_primed
let sys_vars_pr g = g.sys_vars_primed
let prime = Cudd.Bdd.varmap
let man g = g.man

type boolean_formula =
  | And of (boolean_formula * boolean_formula)
  | Or of (boolean_formula * boolean_formula)
  | Xor of (boolean_formula * boolean_formula)
  | Not of boolean_formula
  | Bool of bool
  | Var of string

let bit_blast_int i =
  let nth_bit x n = Bool (x land (1 lsl n) <> 0) in
  let fl = float_of_int i in
  let len = Float.round_up (log fl /. log 2.0) |> int_of_float in
  List.(range 0 len |> map ~f:(nth_bit i))

let bit_blast_var = function
  | Syntax.BoolVarDef _ -> None
  | Syntax.IntVarDef (v, _, u) ->
    let uf = float_of_int u in
    let len = Float.round_up (log uf /. log 2.0) |> int_of_float in
    Some (v, List.(range 0 len
                   |> map ~f:(fun i -> Var ("_" ^ v ^ "_" ^ string_of_int i))))

let ripple_carry_add al bl cin =
  let final_carry = ref (Bool false) in
  let rec rca ~al ~bl ~carry =
    match (al, bl) with
    | (ahd :: atl), (bhd :: btl) ->
      let result = Xor (Xor (ahd, bhd), carry) in
      let next_carry = Or (And (ahd, bhd), And (Xor (ahd, bhd), carry)) in
      result :: (rca ~al:atl ~bl:btl ~carry:next_carry)
    | (ahd :: atl), [] ->
      let result = Xor (ahd, carry) in
      let next_carry = And (ahd, carry) in
      result :: (rca ~al:atl ~bl:[] ~carry:next_carry)
    | [], (bhd :: btl) ->
      let result = Xor (bhd, carry) in
      let next_carry = And (bhd, carry) in
      result :: (rca ~al:[] ~bl:btl ~carry:next_carry)
    | [], [] -> final_carry := carry; []
  in
  match cin with
  | false -> (rca ~al ~bl ~carry:(Bool false), !final_carry)
  | true -> (rca ~al ~bl ~carry:(Bool true), !final_carry)
  
let bitwise_neg = List.map ~f:(fun f -> Not f)

let rec compile_term ~ivar_alist t =
  let compile_term' = compile_term ~ivar_alist in
  let compile_add a b = fst @@ ripple_carry_add a b false in
  let compile_sub a b = fst @@ ripple_carry_add a (bitwise_neg b) true in
  let open Syntax in
  match t with
  | Add (u, r) -> compile_add (compile_term' u) (compile_term' r)
  | Sub (u, r) -> compile_sub (compile_term' u) (compile_term' r)
  (* | Mul (u, r) -> compile_mul (compile_term u) (compile_term r) *)
  (* | Div (u, r) -> compile_div (compile_term u) (compile_term r) *)
  | Int i -> bit_blast_int i
  | Ivar v ->
    match List.Assoc.find ivar_alist ~equal:String.equal v with
    | Some fl -> fl
    | None -> assert false

let compile ~ivar_alist fl =
  let rec compile_f f =
    match f with
    | Syntax.And (g, h) -> And (compile_f g , compile_f h)
    | Syntax.Or (g, h) -> Or (compile_f g, compile_f h)
    | Syntax.Not g -> Not (compile_f g)
    | Syntax.Atom a ->
      let rec compile_eq ts us =
        match (ts, us) with
        | (thd :: ttl), (uhd :: utl) -> And (And (thd, uhd), compile_eq ttl utl)
        | (thd :: ttl), [] -> And (Not thd, compile_eq ttl [])
        | [], (uhd :: utl) -> And (Not uhd, compile_eq [] utl)
        | [], [] -> Bool true
      in
      let compile_lt ts us = snd @@ ripple_carry_add ts (bitwise_neg us) true in (* since a<b == a-b<0 *)
      let compile_term' = compile_term ~ivar_alist in
      match a with
      | Syntax.Bvar v -> Var v
      | Syntax.Bool b -> Bool b
      | Syntax.Eq (t, u) -> compile_eq (compile_term' t) (compile_term' u)
      | Syntax.Lt (t, u) -> compile_lt (compile_term' t) (compile_term' u)
      | Syntax.Gt (t, u) ->
        let t' = compile_term' t and u' = compile_term' u in
        And (Not (compile_lt t' u'), Not (compile_eq t' u'))  (* since a>b == !(a<b) & !(a=b) *)
  in
  List.fold fl ~init:(Bool true) ~f:(fun f1 f2 -> Or(f1, compile_f f2))
  


let rec create_bdd ~man ~var_map bf =
  let create_bdd' = create_bdd ~man ~var_map in
  let open Cudd.Bdd in
  match bf with
  | And (a, b) -> dand (create_bdd' a) (create_bdd' b)
  | Or (a, b) -> dor (create_bdd' a) (create_bdd' b)
  | Xor (a, b) -> xor (create_bdd' a) (create_bdd' b)
  | Not a -> dnot (create_bdd' a)
  | Bool true -> dtrue man
  | Bool false -> dfalse man
  | Var v -> ithvar man (Map.find_exn var_map v)

let make_game tree =
  let add_primes vars = vars @ List.map vars
                          ~f:Syntax.( function
                              | BoolVarDef v -> BoolVarDef (v^"'")
                              | IntVarDef (v,l,u) -> IntVarDef (v^"'",l,u)
                            )
  in
  let all_env_vars = add_primes tree.Syntax.env_vars in
  let all_sys_vars = add_primes tree.Syntax.sys_vars in
  
  let bbf = List.filter_map ~f:bit_blast_var in
  let env_ivar_alist = bbf all_env_vars in
  let sys_ivar_alist = bbf all_sys_vars in
  let filter_bvars = Syntax.(function
    | BoolVarDef b -> Some (Var b)
    | IntVarDef _ -> None)
  in
  let env_bvars = List.filter_map ~f:filter_bvars all_env_vars in
  let sys_bvars = List.filter_map ~f:filter_bvars all_sys_vars in
  let num_ivars =
    let count = List.fold ~init:0 ~f:(fun a pr -> a + List.length (snd pr))  in
    (count env_ivar_alist) + (count sys_ivar_alist)
  in
  let num_bvars = List.(length env_bvars + length sys_bvars) in
  let numVars = num_ivars + num_bvars in
  let man = Cudd.Man.make_d ~numVars () in
  let all_formula_vars = List.(rev_append
                                 (rev_append env_bvars sys_bvars)
                                 (rev_append (concat (map ~f:snd env_ivar_alist))
                                    (concat (map ~f:snd sys_ivar_alist))))
  in
  let var_indices = 
    let var_strings = List.map ~f:
        (function
          | Var v -> v
          | _ -> assert false)  (* This should probably be enforced at type level... polymorphic variant?? *)
        all_formula_vars
    in
    List.mapi ~f:(fun i v -> (v,i)) var_strings
  in
  let var_map = Map.of_alist_exn (module String) var_indices in
  let prime_varmap_arr =
    let n = (List.length all_formula_vars) / 2 in
    Array.init n ~f:(fun i -> i + n)
  in

  Cudd.Man.set_varmap man prime_varmap_arr;
  
  let ivar_alist = env_ivar_alist @ sys_ivar_alist in
  let compile_to_bdd fl = create_bdd ~man ~var_map (compile ~ivar_alist fl) in 
  let env_init = compile_to_bdd tree.Syntax.env_init in
  let sys_init = compile_to_bdd tree.Syntax.sys_init in
  let env_trans = compile_to_bdd tree.Syntax.env_trans in
  let sys_trans = compile_to_bdd tree.Syntax.sys_trans in
  let sys_goals = compile_to_bdd tree.Syntax.sys_goals in
  (*  TODO: Definitely clean this up!!!*)
  let env_vars_primed =
    let non_pr_env_bvars =  List.filter_map ~f:filter_bvars tree.Syntax.env_vars in
    let non_pr_env_ivars = List.(concat (map ~f:snd (bbf tree.Syntax.env_vars))) in
    let non_pr_env_indices = List.map (non_pr_env_bvars @ non_pr_env_ivars) ~f:(
        function
        | Var v -> Map.find_exn var_map v
        | _ -> assert false)
    in
    prime Cudd.Bdd.(List.fold non_pr_env_indices ~init:(dtrue man) ~f:(fun acc i -> dand acc (ithvar man i)))
  in
  let sys_vars_primed =
    let non_pr_sys_bvars =  List.filter_map ~f:filter_bvars tree.Syntax.env_vars in
    let non_pr_sys_ivars = List.(concat (map ~f:snd (bbf tree.Syntax.env_vars))) in
    let non_pr_sys_indices = List.map (non_pr_sys_bvars @ non_pr_sys_ivars) ~f:(
        function
        | Var v -> Map.find_exn var_map v
        | _ -> assert false)
    in
    prime Cudd.Bdd.(List.fold non_pr_sys_indices ~init:(dtrue man) ~f:(fun acc i -> dand acc (ithvar man i)))
  in
  { man;
    env_init;
    sys_init;
    env_trans;
    sys_trans;
    sys_goals;
    env_vars_primed;
    sys_vars_primed;
  }
