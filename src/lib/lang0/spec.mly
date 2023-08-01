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

// arrows
%token LEFTARROW0  // ←
%token LEFTARROW1  // ⇐
%token RIGHTARROW0 // →
%token RIGHTARROW1 // ⇒
%token MULTIMAP    // ⊸
%token UPARROW1    // ⇑
%token DOWNARROW1  // ⇓
%right RIGHTARROW0
%right MULTIMAP

// products
%token TIMES  // ×
%token OTIMES // ⊗
%right TIMES
%right OTIMES

// unit
%token TOP
%token UNIT_TYPE // unit

// bool
%token BOOL_TYPE  // bool
%token BOOL_TRUE  // true
%token BOOL_FALSE // false
%token BOOL_AND   // &&
%token BOOL_OR    // ||
%left BOOL_AND
%left BOOL_OR

// nat
%token NAT_TYPE // nat
%token NAT_ZERO // O
%token NAT_SUCC // S
%token NAT_ADD  // +
%token NAT_SUB  // -
%token NAT_MUL  // *
%token NAT_DIV  // /
%token NAT_MOD  // %
%token NAT_LTE  // <=
%token NAT_GTE  // >=
%token NAT_LT   // <
%token NAT_GT   // >
%token NAT_EQ   // ==
%token NAT_NEQ  // !=
%left NAT_ADD
%left NAT_SUB
%left NAT_MUL
%left NAT_DIV
%left NAT_MOD
%left NAT_LTE
%left NAT_GTE
%left NAT_LT
%left NAT_GT
%left NAT_EQ
%left NAT_NEQ

// string
%token<int> CHAR
%token<int list> STRING
%token STR_CAT // ^
%left STR_CAT

// list
%token LIST_CONS // ::
%right LIST_CONS

// bottom
%token BOT // ⊥

// equality
%token EQUAL  // =
%token EQUIV  // ≡
%token NEGATE // ¬
%left EQUIV

// separators
%token PIPE   // |
%token DOT    // .
%token COLON  // :
%token COMMA  // ,
%token SEMI   // ;
%token BULLET // •
%right SEMI

// sort
%token SORT_U // U
%token SORT_L // U

// prim
%token PRIM_STDIN  // stdin
%token PRIM_STDOUT // stdout
%token PRIM_STDERR // stderr

// identifier
%token<int> INTEGER
%token<string> IDENTIFIER

// tm
%token TM_TYPE     // Type
%token TM_FORALL   // forall
%token TM_FN       // fn
%token TM_LN       // fn
%token TM_FUNCTION // function
%token TM_LET      // let
%token TM_IN       // in
%token TM_EXISTS   // exists
%token TM_TUP      // tup
%token TM_MATCH    // match
%token TM_AS       // as
%token TM_WITH     // with
%token TM_IF       // if
%token TM_THEN     // then
%token TM_ELSE     // else
%token TM_REFL     // refl
%token TM_ABSURD   // absurd
%token TM_REW      // rew
%token TM_IO       // IO
%token TM_RETURN   // return
%token TM_PROTO    // proto
%token TM_END      // end
%token TM_CH       // ch⟨
%token TM_HC       // hc⟨
%token TM_OPEN     // open
%token TM_FORK     // fork
%token TM_RECV     // recv
%token TM_SEND     // send
%token TM_CLOSE    // close
%token TM_SLEEP    // sleep
%token TM_RAND     // rand

// modifiers
%token MOD_PROGRAM        // program
%token MOD_LOGICAL        // logical
%token MOD_MULTIPLICATIVE // multiplicative
%token MOD_ADDITIVE       // additive
%token MODIFIER           // #[

// dcl
%token DCL_DEF            // def
%token DCL_INDUCTIVE      // inductive
%token DCL_WHERE          // where

%{ open Syntax %}

%start <dcls> main

%%

let main :=
  | EOF; { [] }
