%{
    open Syntax
%}

%token <int> INT
%token <string> VAR
%token <string> VARPRIME
%token TRUE
%token FALSE
%token LPAREN RPAREN RBRACK LBRACK COLON ELLIPSIS
%token AND OR NOT IMPL /* BIIMPL */
%token LT EQ GT /* NEQ GTEQ LTEQ */
%token ADD SUB /* MUL DIV */
%token ENV_VARS SYS_VARS ENV_INIT SYS_INIT ENV_TRANS SYS_TRANS SYS_GOALS WEIGHTS
%token EOF
%left IMPL
%left SUB
%left ADD
%left OR                        /* MUL */
%left AND                       /* DIV */
%nonassoc NOT
%start <Syntax.t option> file
%%

let file :=
  | EOF; { None }
  | env_vars  = loption(env_vars);
    sys_vars  = loption(sys_vars);
    env_init  = loption(env_init);
    sys_init  = loption(sys_init);
    env_trans = loption(env_trans);
    sys_trans = loption(sys_trans);
    sys_goals = loption(sys_goals);
    weights   = loption(weights); EOF;
    { Some
        { env_vars;
          sys_vars;
          env_init;
          sys_init;
          env_trans;
          sys_trans;
          sys_goals;
          weights;
        }
    }

let env_vars == ENV_VARS; ~ = var_def*;                 <>
let sys_vars == SYS_VARS; ~ = var_def*;                 <>
let env_init == ENV_INIT; ~ = formula(non_prime)*;      <>
let sys_init == SYS_INIT; ~ = formula(non_prime)*;      <>
let env_trans == ENV_TRANS; ~ = formula(with_prime)*;   <>
let sys_trans == SYS_TRANS; ~ = formula(with_prime)*;   <>
let sys_goals == SYS_GOALS; ~ = formula(with_prime)*;   <>
let weights == WEIGHTS; ~ = weight_def*;                <>

let var_def :=
  | v = non_prime; COLON; LBRACK; l = INT; ELLIPSIS; u = INT; RBRACK;
    <IntVarDef>
  | v = non_prime;                        <BoolVarDef>

let weight_def ==
  f = formula(with_prime); COLON; i = INT; <>

let formula(v) :=
  | LPAREN; f = formula(v); RPAREN;       <>
  | f = formula(v); AND; g = formula(v);  <And>
  | f = formula(v); OR; g = formula(v);   <Or>
  | NOT; f = formula(v);                  <Not>
  | f = formula(v); IMPL; g = formula(v); { Or (Not f, g) }
  | a = atom(v);                          <Atom>

let atom(v) :=
  | t = term(v); LT; u = term(v);         <Lt>
  | t = term(v); GT; u = term(v);         <Gt>
  | t = term(v); EQ; u = term(v);         <Eq>
  | ~ = v;                                <Bvar>
  | TRUE;                                 { Bool true }
  | FALSE;                                { Bool false }

let term(v) :=
  | LPAREN; t = term(v); RPAREN;          <>
  | t = term(v); ADD; u = term(v);        <Add>
  | t = term(v); SUB; u = term(v);        <Sub>
  /* | t = term(v); MUL; u = term(v);        <Mul> */
  /* | t = term(v); DIV; u = term(v);        <Div> */
  | ~ = v;                                <Ivar>
  | i = INT;                              <Int>

let non_prime := v = VAR;                 <>

let with_prime :=
  | v = VARPRIME;                         <>
  | v = VAR;                              <>
