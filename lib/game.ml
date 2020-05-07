open Core

type t = { man : Cudd.Man.dt;
           env_init : bdd;
           sys_init : bdd;
           env_trans : bdd;
           sys_trans : bdd;
           sys_goals : bdd;
           env_vars_primed : bdd;
           sys_vars_primed : bdd;
           weights : bdd Map.M(Int).t;
           var_names : string Map.M(Int).t;
         }

and bdd = Cudd.Bdd.dt

let zero g = Cudd.Bdd.dfalse g.man
let env_init g = g.env_init
let sys_init g = g.sys_init
let env_trans g = g.env_trans
let sys_trans g = g.sys_trans
let sys_goals g = g.sys_goals
let env_vars_primed g = g.env_vars_primed
let sys_vars_primed g = g.sys_vars_primed
let weights g = g.weights
let var_names g = g.var_names
let prime = Cudd.Bdd.varmap
let man g = g.man

let print_id game fmt id = Format.pp_print_string fmt (Map.find_exn (var_names game) id)

let pp_bdd game bdd = Format.printf "%a\n@." (Cudd.Bdd.print (print_id game)) bdd

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
  let len = (Float.round_up (log fl /. log 2.0) |> int_of_float) + 1 in
  List.(range 0 len |> map ~f:(nth_bit i))

let bit_blast_var = function
  | Syntax.BoolVarDef _ -> None
  | Syntax.IntVarDef (v, _, u) ->
    let uf = float_of_int u in
    let len = (Float.round_up (log uf /. log 2.0) |> int_of_float) + 1 in
    Some (v, List.(range 0 len
                   |> map ~f:(fun i -> Var ("_" ^ v ^ "_" ^ string_of_int i))))

let ivar_constrs = function
  | Syntax.BoolVarDef _ -> None
  | Syntax.IntVarDef (v, l, u) ->
    Some Syntax.(And (Or (Atom (Gt (Ivar v, Int l)),
                          Atom (Eq (Ivar v, Int l))),
                      Or (Atom (Lt (Ivar v, Int u)),
                          Atom (Eq (Ivar v, Int u)))))


let equalise_len al bl =
  let rec pad cl n =
    if n = 0 then
      cl
    else
      match cl with
      | (chd :: ctl) -> chd :: pad ctl (n - 1)
      | [] -> (Bool false) :: pad [] (n - 1)
  in
  let open List in
  if length al > length bl then
    (al, pad bl (length al))
  else
    (pad al (length bl), bl)

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
  let result = rca ~al ~bl ~carry:(Bool cin) in
  (result, !final_carry)
  
let bitwise_neg = List.map ~f:(fun f -> Not f)

let rec compile_term ~ivar_alist t =
  let compile_term' = compile_term ~ivar_alist in
  let compile_add a b = fst @@ ripple_carry_add a b false in
  let compile_sub a b =
    let a', b' = equalise_len a b in
    fst @@ ripple_carry_add a' (bitwise_neg b') true in
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
    | None -> raise (Failure v)

let compile ~ivar_alist ?(conjunction=true) fl =
  let rec compile_f f =
    match f with
    | Syntax.And (g, h) -> And (compile_f g , compile_f h)
    | Syntax.Or (g, h) -> Or (compile_f g, compile_f h)
    | Syntax.Not g -> Not (compile_f g)
    | Syntax.Atom a ->
      let rec compile_eq ts us =
        match (ts, us) with
        | (thd :: ttl), (uhd :: utl) -> And (Not (Xor (thd, uhd)), compile_eq ttl utl)
        | (thd :: ttl), [] -> And (Not thd, compile_eq ttl [])
        | [], (uhd :: utl) -> And (Not uhd, compile_eq [] utl)
        | [], [] -> Bool true
      in
      let compile_lt ts us =
        let ts', us' = equalise_len ts us in
        Not (snd @@ ripple_carry_add ts'(bitwise_neg us') true) in (* since a<b == a-b<0 *)
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
  if conjunction then
    List.fold fl ~init:(Bool true) ~f:(fun f1 f2 -> And(f1, compile_f f2))
  else
    List.fold fl ~init:(Bool false) ~f:(fun f1 f2 -> Or(f1, compile_f f2))

  
let rec create_bdd ~man ~var_indices bf =
  let create_bdd' = create_bdd ~man ~var_indices in
  let open Cudd.Bdd in
  match bf with
  | And (a, b) -> dand (create_bdd' a) (create_bdd' b)
  | Or (a, b) -> dor (create_bdd' a) (create_bdd' b)
  | Xor (a, b) -> xor (create_bdd' a) (create_bdd' b)
  | Not a -> dnot (create_bdd' a)
  | Bool true -> dtrue man
  | Bool false -> dfalse man
  | Var v -> ithvar man (Map.find_exn var_indices v)

let make_game tree =
  let make_primes vars = List.map vars
                          ~f:Syntax.(function
                              | BoolVarDef v -> BoolVarDef (v^"'")
                              | IntVarDef (v,l,u) -> IntVarDef (v^"'",l,u)
                            )
  in

  let tr_env_vars = tree.Syntax.env_vars in
  let tr_sys_vars = tree.Syntax.sys_vars in
  
  let tr_env_vars_pr = make_primes tr_env_vars in
  let tr_sys_vars_pr = make_primes tr_sys_vars in
  
  let bbf = List.filter_map ~f:bit_blast_var in
  let env_ivar_alist = bbf tr_env_vars in
  let env_ivar_alist_pr = bbf tr_env_vars_pr in
  let sys_ivar_alist = bbf tr_sys_vars in
  let sys_ivar_alist_pr = bbf tr_sys_vars_pr in
  
  let filter_bvars = Syntax.(function
    | BoolVarDef b -> Some (Var b)
    | IntVarDef _ -> None)
  in
  let env_bvars = List.filter_map ~f:filter_bvars tr_env_vars in
  let env_bvars_pr = List.filter_map ~f:filter_bvars tr_env_vars_pr in
  let sys_bvars = List.filter_map ~f:filter_bvars tr_sys_vars in
  let sys_bvars_pr = List.filter_map ~f:filter_bvars tr_sys_vars_pr in
  
  let num_ivars =
    let count = List.fold ~init:0 ~f:(fun a pr -> a + List.length (snd pr))  in
    (count env_ivar_alist) + (count env_ivar_alist_pr) +
    (count sys_ivar_alist) + (count sys_ivar_alist_pr)
  in
  let num_bvars = List.(length env_bvars + length env_bvars_pr +
                        length sys_bvars + length sys_bvars_pr) in
  let numVars = num_ivars + num_bvars in
  let man = Cudd.Man.make_d ~numVars () in

  let all_formula_vars =
    let open List in
    env_bvars @ sys_bvars @
    (concat (map ~f:snd env_ivar_alist)) @ (concat (map ~f:snd sys_ivar_alist)) @
    env_bvars_pr @ sys_bvars_pr @
    (concat (map ~f:snd env_ivar_alist_pr)) @ (concat (map ~f:snd sys_ivar_alist_pr))
  in                            (* Absolutely horrendous, please see me after the lesson *)
  
  let var_indices_alist =
    let var_strings = List.map ~f:
        (function
          | Var v -> v
          | _ -> assert false)  (* This should probably be enforced at type level... polymorphic variant?? *)
        all_formula_vars
    in
    List.mapi ~f:(fun i v -> (v,i)) var_strings
  in
  let var_indices = Map.of_alist_exn (module String) var_indices_alist in
  
  let prime_varmap_arr =
    let n = (List.length all_formula_vars) / 2 in (* a_f_vs will always be even length *)
    Array.init n ~f:(fun i -> i + n)
  in

  Cudd.Man.set_varmap man prime_varmap_arr;

  let env_vars_primed =
    let evars_pr = env_bvars_pr @ List.(concat (map env_ivar_alist_pr ~f:snd)) in
    let evar_indices_pr = List.map evars_pr ~f:(function
        | Var v -> Map.find_exn var_indices v
        | _ -> assert false) in
    Cudd.Bdd.( List.fold evar_indices_pr ~init:(dtrue man)  ~f:(fun acc i -> dand acc (ithvar man i)))
  in

  let sys_vars_primed =
    let svars_pr = sys_bvars_pr @ List.(concat (map sys_ivar_alist_pr ~f:snd)) in
    let svar_indices_pr = List.map svars_pr ~f:(function
        | Var v -> Map.find_exn var_indices v
        | _ -> assert false) in
    Cudd.Bdd.(List.fold svar_indices_pr ~init:(dtrue man)  ~f:(fun acc i -> dand acc (ithvar man i)))
  in
  
  let ivar_alist = env_ivar_alist @ sys_ivar_alist @ env_ivar_alist_pr @ sys_ivar_alist_pr in
  let compile_to_bdd fl = create_bdd ~man ~var_indices (compile ~ivar_alist fl) in 
  let env_init = compile_to_bdd tree.Syntax.env_init in
  let sys_init = compile_to_bdd tree.Syntax.sys_init in

  let env_ivar_constr = List.filter_map ~f:ivar_constrs tr_env_vars in
  let sys_ivar_constr = List.filter_map ~f:ivar_constrs tr_sys_vars in
  let env_trans = compile_to_bdd (env_ivar_constr @ tree.Syntax.env_trans) in
  let sys_trans = compile_to_bdd (sys_ivar_constr @ tree.Syntax.sys_trans) in
  let sys_goals =
    match tree.Syntax.sys_goals with
    | [] -> compile_to_bdd []
    | sgl -> create_bdd ~man ~var_indices (compile ~ivar_alist ~conjunction:false sgl)
  in

  let weights =
    let raw = List.map tree.Syntax.weights ~f:(fun (formula, n) -> (n, compile_to_bdd [formula])) in
    
    let unionPut map key data =
      Map.update map key
        ~f:(function
          | None -> data
          | Some s -> Cudd.Bdd.dor s data)
    in
    
    List.fold raw ~init:(Map.singleton (module Int) 0 (Cudd.Bdd.dtrue man)) ~f:(fun prev (w, s) ->
        Map.fold prev ~init:(Map.empty (module Int)) ~f:(fun ~key ~data tempMap -> 
            Cudd.Bdd.(
              let t' = unionPut tempMap (key + w) (dand data s) in
              unionPut t' key (dand data (dnot s)))))
    |> Map.filter ~f:(fun v -> not (Cudd.Bdd.is_false v))
  in

  let var_names =
    Map.(fold var_indices ~init:(empty (module Int)) ~f:(fun ~key ~data acc ->
        add_exn acc ~key:data ~data:key)) (* reverse the map *)
  in
  
  { man;
    env_init;
    sys_init;
    env_trans;
    sys_trans;
    sys_goals;
    env_vars_primed;
    sys_vars_primed;
    weights;
    var_names;
  }



(* TESTS *)
let%expect_test "game_from_slugs_simple_wts" =
  let tree = { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
               sys_vars = [(Syntax.BoolVarDef "x"); (Syntax.BoolVarDef "y")];
               env_init =
                 [(Syntax.And
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "a"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "b")))))
                 ];
               sys_init =
                 [(Syntax.And
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "x"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "y")))))
                 ];
               env_trans =
                 [(Syntax.Or
                     ((Syntax.Atom (Syntax.Bvar "a'")),
                      (Syntax.Not
                         (Syntax.Or
                            ((Syntax.Atom (Syntax.Bvar "x")),
                             (Syntax.Atom (Syntax.Bvar "y")))))))
                 ];
               sys_trans =
                 [(Syntax.Or
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "x'"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "y'")))))
                 ];
               sys_goals =
                 [(Syntax.And
                     ((Syntax.Atom (Syntax.Bvar "a")), (Syntax.Atom (Syntax.Bvar "y"))))
                 ];
               weights =
                 [((Syntax.Atom (Syntax.Bvar "y")), -1);
                  ((Syntax.Atom (Syntax.Bvar "x")), 1)]
             }
  in
  let game = make_game tree in
  printf "%s" "env_init: ";
  pp_bdd game game.env_init;
  printf "%s" "sys_init: ";
  pp_bdd game game.sys_init;
  printf "%s" "env_trans: ";
  pp_bdd game game.env_trans;
  printf "%s" "sys_trans: ";
  pp_bdd game game.sys_trans;
  printf "%s" "sys_goals: ";
  pp_bdd game game.sys_goals;
  printf "%s" "env_vars_primed: ";
  pp_bdd game game.env_vars_primed;
  printf "%s" "sys_vars_primed: ";
  pp_bdd game game.sys_vars_primed;
  printf "%s" "weights: ";
  Map.iteri game.weights ~f:(fun ~key ~data ->
      printf "%d = " key;
      pp_bdd game data;);
  [%expect {|
    env_init: !b^!a

    sys_init: !y^!x

    env_trans: ITE(x;a';ITE(y;a';true))

    sys_trans: ITE(x';!y';true)

    sys_goals: y^a

    env_vars_primed: b'^a'

    sys_vars_primed: y'^x'

    weights: -1 = y^!x

    0 = ITE(x;y;!y)

    1 = !y^x |}]

let%expect_test "game_from_basic_bints" =
  let tree = { Syntax.env_vars =
                 [(Syntax.IntVarDef ("a", 0, 4)); (Syntax.IntVarDef ("b", 0, 4))];
               sys_vars = [(Syntax.IntVarDef ("x", 0, 2))]; env_init = []; sys_init = [];
               env_trans =
                 [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "a'"), (Syntax.Ivar "b'"))))];
               sys_trans = [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "x'"), (Syntax.Int 2))))];
               sys_goals = []; weights = [] }
  in
  let game = make_game tree in
  printf "%s" "env_init: ";
  pp_bdd game game.env_init;
  printf "%s" "sys_init: ";
  pp_bdd game game.sys_init;
  printf "%s" "env_trans: ";
  pp_bdd game game.env_trans;
  printf "%s" "sys_trans: ";
  pp_bdd game game.sys_trans;
  printf "%s" "sys_goals: ";
  pp_bdd game game.sys_goals;
  printf "%s" "env_vars_primed: ";
  pp_bdd game game.env_vars_primed;
  printf "%s" "sys_vars_primed: ";
  pp_bdd game game.sys_vars_primed;
  printf "%s" "weights: ";
  Map.iteri game.weights ~f:(fun ~key ~data ->
      printf "%d = " key;
      pp_bdd game data;);
  [%expect {|
    env_init: true

    sys_init: true

    env_trans: ITE(_a_0;
        !_a_2^ITE(_b_0;
                  !_b_2^ITE(_a'_0;
                            _b'_0^ITE(_a'_1;
                                      _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                      !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                            !_b'_0^ITE(_a'_1;
                                       _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                       !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                  ITE(_b_1;
                      !_b_2^ITE(_a'_0;
                                _b'_0^ITE(_a'_1;
                                          _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                          !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                                !_b'_0^ITE(_a'_1;
                                           _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                           !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                      ITE(_a'_0;
                          _b'_0^ITE(_a'_1;
                                    _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                    !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                          !_b'_0^ITE(_a'_1;
                                     _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                     !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)))));
        ITE(_a_1;
            !_a_2^ITE(_b_0;
                      !_b_2^ITE(_a'_0;
                                _b'_0^ITE(_a'_1;
                                          _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                          !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                                !_b'_0^ITE(_a'_1;
                                           _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                           !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                      ITE(_b_1;
                          !_b_2^ITE(_a'_0;
                                    _b'_0^ITE(_a'_1;
                                              _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                              !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                                    !_b'_0^ITE(_a'_1;
                                               _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                               !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                          ITE(_a'_0;
                              _b'_0^ITE(_a'_1;
                                        _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                        !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                              !_b'_0^ITE(_a'_1;
                                         _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                         !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)))));
            ITE(_b_0;
                !_b_2^ITE(_a'_0;
                          _b'_0^ITE(_a'_1;
                                    _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                    !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                          !_b'_0^ITE(_a'_1;
                                     _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                     !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                ITE(_b_1;
                    !_b_2^ITE(_a'_0;
                              _b'_0^ITE(_a'_1;
                                        _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                        !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                              !_b'_0^ITE(_a'_1;
                                         _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                         !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)));
                    ITE(_a'_0;
                        _b'_0^ITE(_a'_1;
                                  _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                  !_b'_1^ITE(_a'_2;_b'_2;!_b'_2));
                        !_b'_0^ITE(_a'_1;
                                   _b'_1^ITE(_a'_2;_b'_2;!_b'_2);
                                   !_b'_1^ITE(_a'_2;_b'_2;!_b'_2)))))))

    sys_trans: _x'_1^!_x'_0^ITE(_x_0;!_x_1;true)

    sys_goals: true

    env_vars_primed: _b'_2^_b'_1^_b'_0^_a'_2^_a'_1^_a'_0

    sys_vars_primed: _x'_1^_x'_0

    weights: 0 = true |}]


let%expect_test "game_from_simple_bints" =
  let tree = { Syntax.env_vars =
                 [(Syntax.IntVarDef ("a", 0, 4)); (Syntax.IntVarDef ("b", 0, 4))];
               sys_vars = [(Syntax.IntVarDef ("x", 0, 2))]; env_init = []; sys_init = [];
               env_trans =
                 [(Syntax.Or
                     ((Syntax.Not
                         (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "a"), (Syntax.Ivar "b"))))),
                      (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "b'"), (Syntax.Int 0))))))
                 ];
               sys_trans =
                 [(Syntax.Or
                     ((Syntax.Not
                         (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "a"), (Syntax.Int 4))))),
                      (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "x'"), (Syntax.Int 0))))))
                 ];
               sys_goals = []; weights = [] }
  in
  let game = make_game tree in
  printf "%s" "env_init: ";
  pp_bdd game game.env_init;
  printf "%s" "sys_init: ";
  pp_bdd game game.sys_init;
  printf "%s" "env_trans: ";
  pp_bdd game game.env_trans;
  printf "%s" "sys_trans: ";
  pp_bdd game game.sys_trans;
  printf "%s" "sys_goals: ";
  pp_bdd game game.sys_goals;
  printf "%s" "env_vars_primed: ";
  pp_bdd game game.env_vars_primed;
  printf "%s" "sys_vars_primed: ";
  pp_bdd game game.sys_vars_primed;
  printf "%s" "weights: ";
  Map.iteri game.weights ~f:(fun ~key ~data ->
      printf "%d = " key;
      pp_bdd game data;);
  [%expect {|
    env_init: true

    sys_init: true

    env_trans: ITE(_a_0;
        !_a_2^ITE(_a_1;
                  ITE(_b_0;
                      !_b_2^ITE(_b_1;!_b'_2^!_b'_1^!_b'_0;true);
                      ITE(_b_1;!_b_2;true));
                  ITE(_b_0;
                      !_b_2^ITE(_b_1;true;!_b'_2^!_b'_1^!_b'_0);
                      ITE(_b_1;!_b_2;true)));
        ITE(_a_1;
            !_a_2^ITE(_b_0;!_b_2;ITE(_b_1;!_b'_2^!_b'_1^!_b'_0^!_b_2;true));
            ITE(_a_2;
                ITE(_b_0;
                    !_b_2;
                    ITE(_b_1;!_b_2;ITE(_b_2;!_b'_2^!_b'_1^!_b'_0;true)));
                ITE(_b_0;
                    !_b_2;
                    ITE(_b_1;!_b_2;ITE(_b_2;true;!_b'_2^!_b'_1^!_b'_0))))))

    sys_trans: ITE(_a_0;
        ITE(_x_0;!_x_1;true);
        ITE(_a_1;
            ITE(_x_0;!_x_1;true);
            ITE(_a_2;!_x'_1^!_x'_0^ITE(_x_0;!_x_1;true);ITE(_x_0;!_x_1;true))))

    sys_goals: true

    env_vars_primed: _b'_2^_b'_1^_b'_0^_a'_2^_a'_1^_a'_0

    sys_vars_primed: _x'_1^_x'_0

    weights: 0 = true |}]

let%expect_test "game_from_no_goals" =
  let tree = { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
               sys_vars = [(Syntax.BoolVarDef "x"); (Syntax.BoolVarDef "y")];
               env_init =
                 [(Syntax.And
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "a"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "b")))))
                 ];
               sys_init =
                 [(Syntax.And
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "x"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "y")))))
                 ];
               env_trans =
                 [(Syntax.Or
                     ((Syntax.Atom (Syntax.Bvar "a'")),
                      (Syntax.Not
                         (Syntax.Or
                            ((Syntax.Atom (Syntax.Bvar "x")),
                             (Syntax.Atom (Syntax.Bvar "y")))))))
                 ];
               sys_trans =
                 [(Syntax.Or
                     ((Syntax.Not (Syntax.Atom (Syntax.Bvar "x'"))),
                      (Syntax.Not (Syntax.Atom (Syntax.Bvar "y'")))))
                 ];
               sys_goals = []; weights = [] } 
  in
  let game = make_game tree in
  printf "%s" "env_init: ";
  pp_bdd game game.env_init;
  printf "%s" "sys_init: ";
  pp_bdd game game.sys_init;
  printf "%s" "env_trans: ";
  pp_bdd game game.env_trans;
  printf "%s" "sys_trans: ";
  pp_bdd game game.sys_trans;
  printf "%s" "sys_goals: ";
  pp_bdd game game.sys_goals;
  printf "%s" "env_vars_primed: ";
  pp_bdd game game.env_vars_primed;
  printf "%s" "sys_vars_primed: ";
  pp_bdd game game.sys_vars_primed;
  printf "%s" "weights: ";
  Map.iteri game.weights ~f:(fun ~key ~data ->
      printf "%d = " key;
      pp_bdd game data;);
  [%expect {|
    env_init: !b^!a

    sys_init: !y^!x

    env_trans: ITE(x;a';ITE(y;a';true))

    sys_trans: ITE(x';!y';true)

    sys_goals: true

    env_vars_primed: b'^a'

    sys_vars_primed: y'^x'

    weights: 0 = true |}]
