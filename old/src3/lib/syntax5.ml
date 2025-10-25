open Names

type expr =
  | Var of Name.t
  | Ctag of Constr.t
  | CtagOf of expr
  (* primitive terms *)
  | Int of int
  | Char of char
  (* erasure *)
  | NULL

and exprs = expr list

type cmd =
  (* core *)
  | Move0 of Name.t * expr
  | Move1 of Name.t * expr
  | Env of Name.t * int
  | MkClo0 of
      { lhs : Name.t
      ; fn : Name.t
      ; fvc : int
      ; argc : int
      }
  | MkClo1 of
      { lhs : Name.t
      ; fn : Name.t
      ; fvc : int
      ; argc : int
      }
  | SetClo of Name.t * expr * int
  | AppF of
      { lhs : Name.t
      ; fn : Name.t
      ; args : exprs
      }
  | AppC of
      { lhs : Name.t
      ; fn : Name.t
      ; arg : expr
      }
  | Free of expr
  (* inductive *)
  | MkBox of
      { lhs : Name.t
      ; ctag : Constr.t
      ; argc : int
      }
  | ReBox of
      { lhs : Name.t
      ; fip : expr
      ; ctag : Constr.t
      }
  | SetBox of Name.t * expr * int
  | GetBox of Name.t * expr * int
  | Switch of
      { cond : expr
      ; cases : cases
      }
  | Break
  | Absurd
  (* lazy *)
  | Lazy of
      { lhs : Name.t
      ; fn : Name.t
      ; fvc : int
      }
  | SetLazy of Name.t * expr * int
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
  | Str  of Name.t * string      (* char[] -> string           *)
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
  | Recv0 of Name.t *  expr
  | Recv1 of Name.t *  expr
  | Close0 of Name.t * expr
  | Close1 of Name.t * expr
  (* magic *)
  | Magic

and case =
  | Case of Constr.t * cmds
  | Default of cmds

and cmds = cmd list
and cases = case list

type dcl =
  (* toplevel functions *)
  | DefFun0 of
      { fn : Name.t
      ; args : Name.t list
      ; cmds : cmds
      ; ret : expr
      }
  (* closure functions *)
  | DefFun1 of
      { fn : Name.t
      ; cmds : cmds
      ; ret : expr
      }

type prog = 
  { dcls : dcl list
  ; cmds : cmds
  ; ret : expr
  }
