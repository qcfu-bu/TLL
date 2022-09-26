type id = string [@@deriving show { with_path = false }]
and ids = id list

type sort =
  | U
  | L
[@@deriving show { with_path = false }]

type rel =
  | N
  | R
[@@deriving show { with_path = false }]

type tm =
  | Ann of tm * tm
  | Type of sort
  | Id of id
  | Pi of rel * sort * id * tm * tm
  | Lam of rel * sort * id * tm
  | App of tms
  | Let of rel * id * tm * tm
  | Match of tm * mot * cls
  | Fix of id * tm
[@@deriving show { with_path = false }]

and tms = tm list
and tm_opt = tm option

and mot =
  | Mot0
  | Mot1 of id * tm
  | Mot2 of p * tm
  | Mot3 of id * p * tm

and p =
  | PVar of id
  | PData of id * ids
  | PCons of id * ids

and ps = p list
and cl = p * tm
and cls = cl list

type dcl =
  | DTm of rel * id * tm_opt * tm
  | DData of id * ptl * dconss
  | DAtom of rel * id * tm
[@@deriving show { with_path = false }]

and dcls = dcl list
and dcons = DCons of id * ptl
and dconss = dcons list

and ptl =
  | PBase of tl
  | PBind of id * tm * ptl

and tl =
  | TBase of tm
  | TBind of rel * id * tm * tl
