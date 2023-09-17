open Names

type sort = U | L

type expr =
  | Var of Name.t
  | Ctag of Constr.t
  (* primitive terms *)
  | Int of int
  | Char of char
  (* erasure *)
  | NULL

and exprs = expr list

type cmd =
  (* core *)
  | Move of Name.t * expr
  | Fun of
      { lhs : Name.t
      ; fn : Name.t
      ; args : (sort * Name.t) list
      ; cmds : cmds
      ; ret : expr
      }
  | App of
      { lhs : Name.t
      ; fn : Name.t
      ; args : (sort * expr) list
      }
  | Free of expr
  (* inductive *)
  | MkConstr of
      { lhs : Name.t
      ; fip : expr option
      ; ctag : Constr.t
      ; args : exprs
      }
  | Match0 of
      { cond : expr
      ; cases : cases0
      }
  | Match1 of
      { cond : expr
      ; sort : sort
      ; cases : cases1
      }
  | Absurd
  (* lazy *)
  | Lazy of
      { lhs : Name.t
      ; cmds : cmds
      ; ret : expr
      }
  | Force of Name.t * expr
  (* primitive operators *)
  | Neg  of Name.t * expr        (* int -> int                 *)
  | Add  of Name.t * expr * expr (* int -> int -> int          *)
  | Sub  of Name.t * expr * expr (* int -> int -> int          *)
  | Mul  of Name.t * expr * expr (* int -> int -> int          *)
  | Div  of Name.t * expr * expr (* int -> int -> int          *)
  | Mod  of Name.t * expr * expr (* int -> int -> int          *)
  | Lte  of Name.t * expr * expr (* int -> int -> bool         *)
  | Gte  of Name.t * expr * expr (* int -> int -> bool         *)
  | Lt   of Name.t * expr * expr (* int -> int -> bool         *)
  | Gt   of Name.t * expr * expr (* int -> int -> bool         *)
  | Eq   of Name.t * expr * expr (* int -> int -> bool         *)
  | Chr  of Name.t * expr        (* int -> char                *)
  | Ord  of Name.t * expr        (* char -> int                *)
  | Str of Name.t * string       (* char[] -> string           *)
  | Push of Name.t * expr * expr (* string -> char -> string   *)
  | Cat  of Name.t * expr * expr (* string -> string -> string *)
  | Size of Name.t * expr        (* string -> int              *)
  | Indx of Name.t * expr * expr (* string -> int -> char      *)
  (* primitive effects *)
  | Print of Name.t * expr
  | Prerr of Name.t * expr
  | ReadLn of Name.t * expr
  | Fork of Name.t * expr
  | Send of Name.t * expr * expr 
  | Recv of Name.t * sort * expr
  | Close of Name.t * bool * expr
  (* magic *)
  | Magic

and case0 =
  | Case of Constr.t * cmds
  | Default of cmds

and case1 =
  { ctag : Constr.t
  ; args : (Name.t * bool) list
  ; rhs : cmds
  }

and cmds = cmd list
and cases0 = case0 list
and cases1 = case1 list

type dcl =
  | Main of { cmds : cmds; ret : expr }
  | DefFun of
      { fn : Name.t
      ; args : (sort * Name.t) list
      ; cmds : cmds
      ; ret : expr
      }
  | DefVal of
      { lhs : Name.t
      ; cmds : cmds 
      ; ret : expr
      }

