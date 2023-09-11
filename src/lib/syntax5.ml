open Names

type sort = U | L

type expr =
  | Var of Name.t
  | Ctag of Constr.t
  (* primitive terms *)
  | Int of int
  | Char of char
  | String of string
  (* erasure *)
  | NULL

and exprs = expr list
