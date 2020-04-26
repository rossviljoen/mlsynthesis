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
         }

let acceptStrategy s = s.acceptStrategy
let attractor s = s.attractor
let goodForEnergy s = s.goodForEnergy
let threshold s = s.threshold

let impl g h = Cudd.Bdd.(dor (dnot g) h)

let forceEnvTo game bestT =
  let open Game in
  let open Cudd.Bdd in
  (forall (env_vars_pr game)
     (impl (env_trans game)
        (exist (sys_vars_pr game)
           (dand (sys_trans game) bestT))))     (* I think I finally understand LISP... *)


let rec extents ?(accept=true) ~game ~exts ~maxEng =
  let q =
    if accept then
      Game.sys_goals game
    else
      Cudd.Bdd.dnot (Game.sys_goals game)
  in
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

    let bests = List.(range 0 maxEng |> map ~f:(fun x -> TropicalNat.Int x)) @ [TropicalNat.Inf] in
    let weights = Game.weights game in

    let extsUpToBest exts rem best =
      let open Map in
      let bestT = fold weights ~init:zero
                    ~f:(fun ~key:wt ~data:trans bestT ->
                      let p = fold old ~init:zero
                                ~f:(fun ~key:ev ~data:states p ->
                                  match TropicalNat.(ev - (Int wt)) <= best with
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

  (* let exts =  TODO temp extents stuff*)
    
  let rec calcStrats ~exts ~noAttr ~attractor ~goodForEnergy ~threshold =
    let old = exts in

    let remaining = Cudd.Bdd.dand nonAcceptStates 
                      (Map.fold old
                          ~init:zero
                          ~f:(fun ~key:_ ~data:v a -> Cudd.Bdd.dor v a))
    in

    let bests = List.(range 0 maxEng |> map ~f:(fun x -> TropicalNat.Int x)) @ [TropicalNat.Inf] in
      
    let stratsUpToBest exts noAttr attractor goodForEnergy threshold rem best =
      match best with
      | TropicalNat.Inf -> (exts, noAttr, attractor, goodForEnergy, threshold, rem)
      | TropicalNat.Int n -> 
         let open Map in
         let bestT = fold weights ~init:zero
                       ~f:(fun ~key:wt ~data:trans bestT ->
                         let p = fold old ~init:zero
                                   ~f:(fun ~key:ev ~data:states p ->
                                     match TropicalNat.(ev - (Int wt)) <= best with
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

         let attrB = Cudd.Bdd.dand noAttr b in
         let threshold, attractor, noAttr =
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
         (exts, noAttr, attractor, goodForEnergy, threshold, rem)
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

  let (_, _, attractor, goodForEnergy, threshold) = calcStrats ~exts
    ~noAttr:(nonAcceptStates)
    ~attractor:zero
    ~goodForEnergy:zero
    ~threshold:(Map.empty (module Int))
  in


  { acceptStrategy;
    attractor;
    goodForEnergy;
    threshold;
  }
