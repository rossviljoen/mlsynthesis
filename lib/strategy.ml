open Core

module TropicalNat = struct
  module T = struct
    
    type t = Inf | Int of int
    [@@deriving sexp]

    let (-) n m =
      match n, m with
      | Inf, _ | _, Inf -> Inf
      | Int x, Int y -> Int (max (x - y) 0)

    let compare n m =
      match n, m with
      | Int i, Int j -> Int.compare i j
      | Int _, Inf -> -1
      | Inf, Int _ -> 1
      | Inf, Inf -> 0
  end
  
  include T
  include Comparable.Make(T)
end

type t = { acceptStrategy : Game.bdd;
           attractor : Game.bdd;
           goodForEnergy : Game.bdd;
           threshold : Game.bdd Map.M(Int).t;
           extents : Game.bdd Map.M(TropicalNat).t;
         }

let acceptStrategy s = s.acceptStrategy
let attractor s = s.attractor
let goodForEnergy s = s.goodForEnergy
let threshold s = s.threshold
let getExtents s = s.extents

let pp_tnat = function | TropicalNat.Inf -> print_string "inf: "
                       | TropicalNat.Int n -> Out_channel.output_string stdout ((string_of_int n)^": ")

let pp_extents game map = Map.iteri map ~f:(fun ~key ~data -> pp_tnat key; Game.pp_bdd game data)

let pp_threshold game map = Map.iteri map ~f:(fun ~key ~data ->
    Out_channel.output_string stdout ((string_of_int key)^": "); Game.pp_bdd game data)

let impl g h = Cudd.Bdd.(dor (dnot g) h)

let forceEnvTo game bestT =
  let open Game in
  let open Cudd.Bdd in
  (forall (env_vars_primed game)
     (impl (env_trans game)
        (exist (sys_vars_primed game)
           (dand (sys_trans game) bestT))))     (* I think I finally understand LISP... *)

let minimal_bests ~old ~weights ~maxEng =
  let el = List.filter_map (Map.keys old) ~f:(function
      | TropicalNat.Int n -> Some n
      | TropicalNat.Inf -> None)
  in
  let wl = Map.keys weights in
  let open List in
  concat_map el ~f:(fun e ->
      filter_map wl ~f:(fun w ->
          let b = e - w in
          if (b > 0) && (b <= maxEng) then Some b else None))
  |> map ~f:(fun i -> TropicalNat.Int i) |> fun l -> [TropicalNat.Int 0] @ l @ [TropicalNat.Inf]
                                                     |> dedup_and_sort ~compare:TropicalNat.compare

let rec extents ?(accept=true) ~game ~exts ~maxEng =
  let weights = Game.weights game in
  
  let q =
    if accept then
      Game.sys_goals game
    else
      Cudd.Bdd.dnot (Game.sys_goals game)
  in

  (* Short circuit if all states are accept states (or if none are) *)
  if Cudd.Bdd.is_false q then
    exts
  else
    let notQ = Cudd.Bdd.dnot q in
    let zero = Game.zero game in     (* The zero BDD (representing false) *)

    let exts =
      let otherExts = Map.(map ~f:(Cudd.Bdd.dand notQ) exts) in
      let e = if accept then TropicalNat.Int 0 else TropicalNat.Inf in
      Map.update otherExts e ~f:(function
          | None -> q
          | Some s -> Cudd.Bdd.dor s q
        )
    in

    let rec extents' ~exts =
      let old = exts in
      let exts' =
        if accept then
          extents ~accept:false ~game ~exts ~maxEng
        else
          exts
      in

      let exts = Map.filter_map exts' ~f:(fun v ->
          let v' = Cudd.Bdd.dand v notQ in
          match Cudd.Bdd.is_false v' with
          | true -> None
          | false -> Some v'
        )
      in

      let remaining = Cudd.Bdd.dand q 
          (Map.fold old
             ~init:zero
             ~f:(fun ~key:_ ~data:v a -> Cudd.Bdd.dor v a))
      in

      let bests = minimal_bests ~old ~weights ~maxEng in
      (* let bests = List.(range 0 maxEng |> map ~f:(fun x -> TropicalNat.Int x)) @ [TropicalNat.Inf] in *)

      (* printf "acc: %s -> " (string_of_bool accept); *)
      (* pp_extents game old; *)
      (* Game.pp_bdd game (Map.find_exn weights 0); *)
      (* pp_extents game exts; *)
      (* printf "%s\n" (List.to_string ~f:(fun x -> Sexp.to_string(TropicalNat.sexp_of_t x)) (Map.keys exts)); *)
      (* printf "%s\n" (List.to_string ~f:(fun x -> Sexp.to_string(TropicalNat.sexp_of_t x)) bests); *)

      let extsUpToBest exts rem best =
        let open Map in

        let bestT = fold weights ~init:zero ~f:(fun ~key:wt ~data:trans bestT ->
            let p = fold old ~init:zero ~f:(fun ~key:ev ~data:states p ->
                match TropicalNat.(ev - (Int wt) <= best) with
                | true -> Cudd.Bdd.dor p states
                | false -> p)
            in
            Cudd.Bdd.(dor bestT (dand trans (Game.prime p))))
        in

        let b = Cudd.Bdd.dand (forceEnvTo game bestT) rem in
        let rem = Cudd.Bdd.(dand rem (dnot b)) in

        match (Cudd.Bdd.is_false b) with
        | true -> (exts, rem)
        | false -> (Map.update exts best
                      ~f:(function
                          | None -> b
                          | Some s -> (Cudd.Bdd.dor s b)
                        ), rem)
      in

      let exts, _ = List.fold bests ~init:(exts, remaining)
          ~f:(fun (e, r) b -> extsUpToBest e r b)
      in
      
      if Map.equal Cudd.Bdd.is_equal exts old then exts else extents' ~exts
    in

    extents' ~exts

let solve game maxEng =
  let zero = Game.zero game in
  let weights = Game.weights game in
  let env_trans = Game.env_trans game in
  let sys_trans = Game.sys_trans game in

  let exts = extents ~accept:true ~game ~exts:(Map.empty (module TropicalNat)) ~maxEng in
  
  let acceptStates = Game.sys_goals game in

  let acceptStrategy =
    let possSucc v e =
      let cond ev v e = (ev = max 0 e + v) in
      Map.fold exts ~init:zero
        ~f:(fun ~key ~data p -> match key with
                             | TropicalNat.Inf -> p
                             | TropicalNat.Int ev ->
                                if cond ev v e then Cudd.Bdd.dor p data else p)
    in

    let weightFold ~strat ~rem ~e ~q = 
      Map.fold weights ~init:(strat, rem ,q)
        ~f:(fun ~key ~data (strat, rem, q) ->
          let open Cudd.Bdd in
          let p = possSucc key e in
          let thisT = dand data (Game.prime p) in
          let b = dand (forceEnvTo game thisT) q in
          let strat = (dor
                         (dand strat (dnot b))
                         (dand (dand b thisT)
                            (dand env_trans sys_trans)))
          in
          let q = dand q (dnot b) in
          let rem = dand rem (dnot b)in
          (strat, rem, q)
        )
    in

    Map.fold exts ~init:(zero, Game.sys_goals game)
      ~f:(fun ~key ~data (strat, rem) ->
        match key with
        | Inf -> (strat, rem)
        | Int e -> 
           let (strat, rem, _) =
             weightFold ~strat ~rem ~e ~q:(Cudd.Bdd.dand data acceptStates)
           in
           (strat, rem)) |> fst
  in

  let nonAcceptStates = Cudd.Bdd.dnot acceptStates in

  let exts =
    let otherExts = Map.(map ~f:(Cudd.Bdd.dand acceptStates) exts) in
    Map.update otherExts TropicalNat.Inf ~f:(function
        | None -> nonAcceptStates
        | Some s -> Cudd.Bdd.dor s nonAcceptStates
    )
  in
    
  let rec calcStrats ~exts ~noAttr ~attractor ~goodForEnergy ~threshold =
    let old = exts in

    let exts = Map.filter_map exts ~f:(fun v ->
        let v' = Cudd.Bdd.dand v acceptStates in
        match Cudd.Bdd.is_false v' with
        | true -> None
        | false -> Some v'
      )
    in

    let remaining = Cudd.Bdd.dand nonAcceptStates 
                      (Map.fold old
                          ~init:zero
                          ~f:(fun ~key:_ ~data:v a -> Cudd.Bdd.dor v a))
    in

    let bests = minimal_bests ~old ~weights ~maxEng in
    (* let bests = List.(range 0 maxEng |> map ~f:(fun x -> TropicalNat.Int x)) @ [TropicalNat.Inf] in *)
    
    let stratsUpToBest exts noAttr attractor goodForEnergy threshold rem best =
      let open Map in
      let bestT = fold weights ~init:zero
          ~f:(fun ~key:wt ~data:trans bestT ->
              let p = fold old ~init:zero
                  ~f:(fun ~key:ev ~data:states p ->
                      match TropicalNat.(ev - (Int wt) <= best) with
                      | true -> Cudd.Bdd.dor p states
                      | false -> p)
              in
              Cudd.Bdd.(dor bestT (dand trans (Game.prime p))))
      in
      
      let b = Cudd.Bdd.dand (forceEnvTo game bestT) rem in
      let rem = Cudd.Bdd.(dand rem (dnot b)) in

      let exts = 
        match (Cudd.Bdd.is_false b) with
        | true -> exts
        | false -> Map.update exts best
                     ~f:(function
                         | None -> b
                         | Some s -> Cudd.Bdd.dor s b)
      in

      match best with
      | TropicalNat.Inf -> (exts, noAttr, attractor, goodForEnergy, threshold, rem)
      | TropicalNat.Int n ->
        let attrB = Cudd.Bdd.dand noAttr b in
        let threshold', attractor', noAttr' =
          let open Cudd.Bdd in
          if is_false attrB then
            (threshold, attractor, noAttr)
          else
            let t = Map.update threshold n
                ~f:(function
                    | None -> attrB
                    | Some s -> dor s attrB)
            in
            let a = dor attractor (dand (dand attrB bestT) (dand env_trans sys_trans)) in
            let na = dand noAttr (dnot attrB) in
            (t, a, na)
        in

        let energyB = Cudd.Bdd.(dand (dnot noAttr) b) in
        let goodForEnergy =
          let open Cudd.Bdd in
          if is_false energyB then
            goodForEnergy
          else
            dor (dand goodForEnergy (dnot energyB))
              (dand (dand energyB bestT)
                 (dand env_trans sys_trans))
        in
        (exts, noAttr', attractor', goodForEnergy, threshold', rem)
    in

    let (exts, noAttr, attractor, goodForEnergy, threshold, _) =
      List.fold bests ~init:(exts, noAttr, attractor, goodForEnergy, threshold, remaining)
        ~f:(fun (e, na, a, gfe, t, rem) b -> stratsUpToBest e na a gfe t rem b)
    in

    if Map.equal Cudd.Bdd.is_equal exts old then
      (exts, noAttr, attractor, goodForEnergy, threshold)
    else
      calcStrats ~exts ~noAttr ~attractor ~goodForEnergy ~threshold
  in

  let (extents, _, attractor, goodForEnergy, threshold) = calcStrats ~exts
      ~noAttr:(nonAcceptStates)
      ~attractor:zero
      ~goodForEnergy:zero
      ~threshold:(Map.empty (module Int))
  in

  (* printf "%s\n" (List.to_string ~f:(fun x -> Sexp.to_string(TropicalNat.sexp_of_t x)) (Map.keys exts)); *)
  
  { acceptStrategy;
    attractor;
    goodForEnergy;
    threshold;
    extents;
  }

(* For benchmarking only *)
let calcExtents game maxEng = extents ~accept:true ~game ~exts:(Map.empty (module TropicalNat)) ~maxEng

(* TESTS *)

let%expect_test "strategy_from_slugs_simple_wts" =
  let game = Game.make_game { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
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
  let strat = solve game 40 in
  let pp = Game.pp_bdd game in
  printf "%s" "acceptStrategy: ";
  pp strat.acceptStrategy;
  printf "%s" "attractor: ";
  pp strat.attractor;
  printf "%s" "goodForEnergy: ";
  pp strat.goodForEnergy;
  printf "%s\n" "threshold: ";
  pp_threshold game strat.threshold;
  printf "%s\n" "extents: ";
  pp_extents game strat.extents;
  [%expect {|
    acceptStrategy: !y'^a'^y^a

    attractor: ITE(a;!y^ITE(x;y'^!x'^a';!y'^x');ITE(x;y'^!x'^a';ITE(y;y'^!x'^a';!y'^x')))

    goodForEnergy: ITE(a;
        !y^ITE(x;a'^ITE(x';!y';true);!y');
        ITE(x;a'^ITE(y;!y';ITE(x';!y';true));!y'^ITE(y;a';true)))

    threshold:
    0: !y

    1: y^x^!a

    2: y^!x^!a

    extents:
    0: ITE(x;true;!y)

    1: y^!x |}]

(* let%expect_test "strategy_from_basic_bints" =
 *   let tree = { Syntax.env_vars =
 *                  [(Syntax.IntVarDef ("a", 0, 4)); (Syntax.IntVarDef ("b", 0, 4))];
 *                sys_vars = [(Syntax.IntVarDef ("x", 0, 2))]; env_init = []; sys_init = [];
 *                env_trans =
 *                  [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "a'"), (Syntax.Ivar "b'"))))];
 *                sys_trans = [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "x'"), (Syntax.Int 2))))];
 *                sys_goals = []; weights = [] }
 *   in
 *   let game = Game.make_game tree in
 *   let strat = solve game 40 in
 *   let pp = Game.pp_bdd game in
 *   printf "%s" "acceptStrategy: ";
 *   pp strat.acceptStrategy;
 *   printf "%s" "attractor: ";
 *   pp strat.attractor;
 *   printf "%s" "goodForEnergy: ";
 *   pp strat.goodForEnergy;
 *   printf "%s\n" "threshold: ";
 *   pp_threshold game strat.threshold;
 *   printf "%s\n" "extents: ";
 *   pp_extents game strat.extents;
 *   [%expect {| |}] *)

let%expect_test "strategy_from_no_goals" =
  let game = Game.make_game { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
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
  let strat = solve game 40 in
  let pp = Game.pp_bdd game in
  printf "%s" "acceptStrategy: ";
  pp strat.acceptStrategy;
  printf "%s" "attractor: ";
  pp strat.attractor;
  printf "%s" "goodForEnergy: ";
  pp strat.goodForEnergy;
  printf "%s\n" "threshold: ";
  pp_threshold game strat.threshold;
  printf "%s\n" "extents: ";
  pp_extents game strat.extents;
  [%expect {|
    acceptStrategy: ITE(x;a'^ITE(x';!y';true);ITE(y;a'^ITE(x';!y';true);ITE(x';!y';true)))

    attractor: false

    goodForEnergy: false

    threshold:
    extents:
    0: true |}]
 
