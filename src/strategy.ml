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

(* type t =  *)

(* let solve game = *)
  
let rec extents ?(accept=true) game ext maxRes =
  let q =
    if accept then
      Game.sys_goals game
    else
      Cudd.Bdd.dnot (Game.sys_goals game)
  in
  let notQ = Cudd.Bdd.dnot q in
  
  let ext  =
    let otherExt = Map.(map ~f:(Cudd.Bdd.dand notQ) ext) in
    let e = if accept then TropicalNat.Int 0 else TropicalNat.Inf in
    Map.update otherExt e ~f:(function
        | None -> q
        | Some s -> Cudd.Bdd.dor s q
    )
  in

  let rec extents' ~ext =
    let old = ext in
    let ext' =
      if accept then
        extents ~accept:false game ext maxRes
      else
        ext
    in
    let ext = Map.filter_map ext' ~f:(fun v ->
        let v' = Cudd.Bdd.dand v notQ in
        match Cudd.Bdd.is_false v' with
        | true -> None
        | false -> Some v'
      )
    in

    let zero = Game.zero game in     (* The zero BDD (representing false) *)
    let remaining = Map.fold old
        ~init:zero
        ~f:(fun ~key:_ ~data:v a -> Cudd.Bdd.dor v a)
    in

    let bests = List.(range 0 maxRes |> map ~f:(fun x -> TropicalNat.Int x)) @ [TropicalNat.Inf] in
    let weights = Game.weights game in

    let extUpToBest ext remaining best =
      let open Map in
      let bestT = fold weights ~init:zero ~f:(fun ~key:wt ~data:trans bestT->
          let p = fold old ~init:zero ~f:(fun ~key:ev ~data:states p ->
              match TropicalNat.(ev - (Int wt)) <= best with
              | true -> Cudd.Bdd.dor p states
              | false -> p
            )
          in
          Cudd.Bdd.(dor bestT (dand trans (Game.prime p)))
        )
      in

      let impl g h = Cudd.Bdd.(dor (dnot g) h) in
      let b =
        let open Game in let open Cudd.Bdd in
        (dand remaining
           (forall (env_vars_pr game)
              (impl (env_trans game)
                 (exist (sys_vars_pr game)
                    (dand (sys_trans game) bestT)))))
      in
      let remaining = Cudd.Bdd.(dand remaining (dnot b)) in
      match (Cudd.Bdd.is_false b) with
      | true -> (ext, remaining)
      | false -> (Map.update ext best ~f:(function
          | None -> b
          | Some s -> (Cudd.Bdd.dor s b)
        ), remaining)
    in

    let ext, _ = List.fold bests ~init:(ext, remaining) ~f:(
        fun (e, r) b -> extUpToBest e r b)
    in
    
    if Map.equal Cudd.Bdd.is_equal ext old then ext else extents' ~ext
  in

  extents' ~ext
