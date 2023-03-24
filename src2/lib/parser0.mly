%token EOF

// delimiters
%token LPAREN // (
%token RPAREN // )
%token LBRACK // [
%token RBRACK // ]
%token LBRACE // {
%token RBRACE // {
%token LANGLE // ⟨
%token RANGLE // ⟩
%token FLQ    // ‹
%token FRQ    // ›

// quantifiers
%token FORALL // ∀
%token EXISTS // ∃
%token POS    // !
%token NEG    // ?

// arrows
%token LEFTARROW0  // ←
%token LEFTARROW1  // ⇐
%token RIGHTARROW0 // ←
%token RIGHTARROW1 // ⇐

// products
%token TIMES  // ×
%token OTIMES // ⊗

// arithmetic
%token ARITH_ADD  // +
%token ARITH_SUB  // -
%token ARITH_MUL  // *
%token ARITH_DIV  // /
%token ARITH_MOD  // %
%token ARITH_LTE  // <=
%token ARITH_GTE  // >=
%token ARITH_LT   // <
%token ARITH_GT   // <
%token ARITH_EQ   // ==
%token ARITH_NEQ  // !=

// boolean
%token BOOL_AND // &&
%token BOOL_OR  // ||

// equality
%token EQUAL  // =
%token EQUIV  // ≡
%token NEGATE // ¬

// separators
%token PIPE  // |
%token DOT   // .
%token COLON // :
%token COMMA // ,
%token SEMI  // ;

// sort
%token SORT_U // U
%token SORT_L // U

// prim
%token PRIM_STDIN  // stdin
%token PRIM_STDOUT // stdout
%token PRIM_STDERR // stderr

// identifier
%token<string> IDENTIFIER

// tm
%token TM_FN     // fn
%token TM_LN     // fn
%token TM_LET    // let
%token TM_IN     // in
%token TM_FIX    // fix
%token TM_MATCH  // match
%token TM_WITH   // with
%token TM_REFL   // refl
%token TM_REW    // rew
%token TM_IO     // IO
%token TM_RETURN // return
%token TM_PROTO  // proto
%token TM_END    // end
%token TM_CH     // ch‹
%token TM_HC     // hc‹
%token TM_OPEN   // open
%token TM_FORK   // fork
%token TM_RECV   // recv
%token TM_SEND   // send
%token TM_CLOSE  // close

// dcl
%token DCL_DEFINITION // definition
%token DCL_THEOREM    // theorem
%token DCL_INDUCTIVE  // inductive

// dcons
%token DCONS_OF // of


%{ open Syntax0 %}

%start <tm> main

%%

let identifier :=
  | s = IDENTIFIER; <>

let id :=
  | s = identifier; { Id s }

let main :=
  | ~ = id; EOF; <>
