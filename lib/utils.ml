open Core
open Lexing
open Lexer

let print_id game fmt id = Format.pp_print_string fmt (Map.find_exn (Game.var_names game) id)

let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parser.file Lexer.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    None
  | Parser.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)

let%expect_test "parse_sys_trans_only" =
  let input = {|
    [sys_trans]
    !x & !y
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> List.map ~f:Syntax.show_formula tree.sys_trans
                   |> String.concat;
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    (Syntax.And
       ((Syntax.Not (Syntax.Atom (Syntax.Bvar "x"))),
        (Syntax.Not (Syntax.Atom (Syntax.Bvar "y"))))) |}]

let%expect_test "parse_no_trans" =
  let input = {|
    [env_vars]
    a

    [sys_vars]
    x
    y
    
    [env_init]
    !a & !b

    [sys_init]
    !x & !y

    [sys_goals]
    a & y
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> Syntax.show tree;
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars = [(Syntax.BoolVarDef "a")];
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
      env_trans = []; sys_trans = [];
      sys_goals =
      [(Syntax.And
          ((Syntax.Atom (Syntax.Bvar "a")), (Syntax.Atom (Syntax.Bvar "y"))))
        ];
      weights = [] } |}]

let%expect_test "parse_no_init" =
  let input = {|
    [env_vars]
    a
  
    [sys_vars]
    x
    y

    [env_trans]
    a' | !(x | y)
  
    [sys_trans]
    !x' | !y'
  
    [sys_goals]
    a & y
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> (Syntax.show tree);
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars = [(Syntax.BoolVarDef "a")];
      sys_vars = [(Syntax.BoolVarDef "x"); (Syntax.BoolVarDef "y")];
      env_init = []; sys_init = [];
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
      weights = [] } |}]

let%expect_test "parse_no_goals" =
  let input = {|
    [env_vars]
    a
    b
  
    [sys_vars]
    x
    y
    
    [env_init]
    !a & !b
  
    [sys_init]
    !x & !y
  
    [env_trans]
    a' | !(x | y)
  
    [sys_trans]
    !x' | !y'
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> (Syntax.show tree);
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
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
      sys_goals = []; weights = [] } |}]

let%expect_test "parse_slugs_simple" =
  let inx = In_channel.create "../examples/slugs_simple.in" in
  let lexbuf = Lexing.from_channel inx in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> (Syntax.show tree);
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
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
      weights = [] } |}]

let%expect_test "parse_bints" =
  let input = {|
    [env_vars]
    a      : [0..4]
    b      : [0..4]

    [sys_vars]
    x          : [0..2]

    [env_trans]
    a' = b'

    [sys_trans]
    x = 2
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> Syntax.show tree;
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars =
      [(Syntax.IntVarDef ("a", 0, 4)); (Syntax.IntVarDef ("b", 0, 4))];
      sys_vars = [(Syntax.IntVarDef ("x", 0, 2))]; env_init = []; sys_init = [];
      env_trans =
      [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "a'"), (Syntax.Ivar "b'"))))];
      sys_trans = [(Syntax.Atom (Syntax.Eq ((Syntax.Ivar "x"), (Syntax.Int 2))))];
      sys_goals = []; weights = [] } |}]

let%expect_test "parse_simple_bints" =
  let input = {|
    [env_vars]
    a      : [0..4]
    b      : [0..4]


    [sys_vars]
    x          : [0..2]

    [env_trans]
    a = b -> b' = 0

    [sys_trans]
    a = 4 -> x' = 0
  |}
  in
  let lexbuf = Lexing.from_string input in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> Syntax.show tree;
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars =
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
      sys_goals = []; weights = [] } |}]

let%expect_test "parse_slugs_simple_wts" =
  let inx = In_channel.create "../examples/slugs_simple_wts.in" in
  let lexbuf = Lexing.from_channel inx in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> (Syntax.show tree);
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars = [(Syntax.BoolVarDef "a"); (Syntax.BoolVarDef "b")];
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
      } |}]

let%expect_test "parse_lift" =
  let inx = In_channel.create "../examples/lift.in" in
  let lexbuf = Lexing.from_channel inx in
  let result = 
    match parse_with_error lexbuf with
    | Some tree -> (Syntax.show tree);
    | None -> "No parse tree produced";
  in
  printf "%s" result;
  [%expect {|
    { Syntax.env_vars =
      [(Syntax.BoolVarDef "pending"); (Syntax.IntVarDef ("src_floor", 0, 4));
        (Syntax.IntVarDef ("dest_floor", 0, 4));
        (Syntax.IntVarDef ("current_floor", 0, 4))];
      sys_vars = [(Syntax.IntVarDef ("move", 0, 2))]; env_init = [];
      sys_init = [];
      env_trans =
      [(Syntax.Or
          ((Syntax.Not
              (Syntax.And
                 ((Syntax.Not (Syntax.Atom (Syntax.Bvar "pending"))),
                  (Syntax.Atom (Syntax.Bvar "pending'"))))),
           (Syntax.Atom
              (Syntax.Eq
                 ((Syntax.Ivar "src_floor'"), (Syntax.Ivar "current_floor'"))))));
        (Syntax.Or
           ((Syntax.Not (Syntax.Atom (Syntax.Bvar "pending"))),
            (Syntax.And
               ((Syntax.Atom
                   (Syntax.Eq
                      ((Syntax.Ivar "src_floor'"), (Syntax.Ivar "src_floor")))),
                (Syntax.Atom
                   (Syntax.Eq
                      ((Syntax.Ivar "dest_floor'"), (Syntax.Ivar "dest_floor"))))))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.And
                  ((Syntax.Atom (Syntax.Bvar "pending")),
                   (Syntax.Not
                      (Syntax.Atom
                         (Syntax.Eq
                            ((Syntax.Ivar "current_floor"),
                             (Syntax.Ivar "dest_floor")))))))),
            (Syntax.Atom (Syntax.Bvar "pending'"))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.And
                  ((Syntax.Atom
                      (Syntax.Eq
                         ((Syntax.Ivar "current_floor"),
                          (Syntax.Ivar "dest_floor")))),
                   (Syntax.Atom (Syntax.Bvar "pending"))))),
            (Syntax.Not (Syntax.Atom (Syntax.Bvar "pending'")))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.And
                  ((Syntax.Atom
                      (Syntax.Eq ((Syntax.Ivar "move"), (Syntax.Int 2)))),
                   (Syntax.Atom
                      (Syntax.Lt ((Syntax.Ivar "current_floor"), (Syntax.Int 4))))))),
            (Syntax.Atom
               (Syntax.Eq
                  ((Syntax.Ivar "current_floor'"),
                   (Syntax.Add ((Syntax.Ivar "current_floor"), (Syntax.Int 1))))))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "move"), (Syntax.Int 1))))),
            (Syntax.Atom
               (Syntax.Eq
                  ((Syntax.Ivar "current_floor'"), (Syntax.Ivar "current_floor"))))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.And
                  ((Syntax.Atom
                      (Syntax.Eq ((Syntax.Ivar "move"), (Syntax.Int 0)))),
                   (Syntax.Atom
                      (Syntax.Gt ((Syntax.Ivar "current_floor"), (Syntax.Int 0))))))),
            (Syntax.Atom
               (Syntax.Eq
                  ((Syntax.Ivar "current_floor'"),
                   (Syntax.Sub ((Syntax.Ivar "current_floor"), (Syntax.Int 1))))))))
        ];
      sys_trans =
      [(Syntax.Or
          ((Syntax.Not
              (Syntax.Atom
                 (Syntax.Eq ((Syntax.Ivar "current_floor"), (Syntax.Int 4))))),
           (Syntax.Not
              (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "move"), (Syntax.Int 2)))))));
        (Syntax.Or
           ((Syntax.Not
               (Syntax.Atom
                  (Syntax.Eq ((Syntax.Ivar "current_floor"), (Syntax.Int 0))))),
            (Syntax.Not
               (Syntax.Atom (Syntax.Eq ((Syntax.Ivar "move"), (Syntax.Int 0)))))))
        ];
      sys_goals = [];
      weights =
      [((Syntax.And
           ((Syntax.Atom (Syntax.Bvar "pending")),
            (Syntax.Not
               (Syntax.Atom
                  (Syntax.Eq
                     ((Syntax.Ivar "current_floor"), (Syntax.Ivar "dest_floor"))))))),
        -1);
        ((Syntax.Or
            ((Syntax.And
                ((Syntax.And
                    ((Syntax.Atom (Syntax.Bvar "pending")),
                     (Syntax.Not (Syntax.Atom (Syntax.Bvar "pending'"))))),
                 (Syntax.Atom
                    (Syntax.Eq
                       ((Syntax.Sub
                           ((Syntax.Ivar "src_floor"), (Syntax.Ivar "dest_floor"))),
                        (Syntax.Int 1)))))),
             (Syntax.Atom
                (Syntax.Eq
                   ((Syntax.Sub
                       ((Syntax.Ivar "dest_floor"), (Syntax.Ivar "src_floor"))),
                    (Syntax.Int 1)))))),
         1);
        ((Syntax.Or
            ((Syntax.And
                ((Syntax.And
                    ((Syntax.Atom (Syntax.Bvar "pending")),
                     (Syntax.Not (Syntax.Atom (Syntax.Bvar "pending'"))))),
                 (Syntax.Atom
                    (Syntax.Eq
                       ((Syntax.Sub
                           ((Syntax.Ivar "src_floor"), (Syntax.Ivar "dest_floor"))),
                        (Syntax.Int 2)))))),
             (Syntax.Atom
                (Syntax.Eq
                   ((Syntax.Sub
                       ((Syntax.Ivar "dest_floor"), (Syntax.Ivar "src_floor"))),
                    (Syntax.Int 2)))))),
         2);
        ((Syntax.Or
            ((Syntax.And
                ((Syntax.And
                    ((Syntax.Atom (Syntax.Bvar "pending")),
                     (Syntax.Not (Syntax.Atom (Syntax.Bvar "pending'"))))),
                 (Syntax.Atom
                    (Syntax.Eq
                       ((Syntax.Sub
                           ((Syntax.Ivar "src_floor"), (Syntax.Ivar "dest_floor"))),
                        (Syntax.Int 3)))))),
             (Syntax.Atom
                (Syntax.Eq
                   ((Syntax.Sub
                       ((Syntax.Ivar "dest_floor"), (Syntax.Ivar "src_floor"))),
                    (Syntax.Int 3)))))),
         3);
        ((Syntax.Or
            ((Syntax.And
                ((Syntax.And
                    ((Syntax.Atom (Syntax.Bvar "pending")),
                     (Syntax.Not (Syntax.Atom (Syntax.Bvar "pending'"))))),
                 (Syntax.Atom
                    (Syntax.Eq
                       ((Syntax.Sub
                           ((Syntax.Ivar "src_floor"), (Syntax.Ivar "dest_floor"))),
                        (Syntax.Int 4)))))),
             (Syntax.Atom
                (Syntax.Eq
                   ((Syntax.Sub
                       ((Syntax.Ivar "dest_floor"), (Syntax.Ivar "src_floor"))),
                    (Syntax.Int 4)))))),
         4)
        ]
      } |}]
