open Names

(* syntax definitions *)
type id = string
type ids = id list
type sort = U | L
type rel = N | R
type role = Pos | Neg
type prim = Stdin | Stdout | Stderr
type 'a binder = Binder of id * 'a
type 'a mbinder = MBinder of ids * 'a

type tm =
  (* inference *)
  | Ann of tm * tm
  (* core *)
  | Id of id
  | Type of sort
  | Pi of rel * sort * tm * tm binder
  | Lam of rel * sort * tm binder
  | App of tms
  | Let of rel * tm * tm binder
  | Fix of tm binder
  (* data *)
  | Sigma of rel * sort * tm * tm binder
  | Pair of rel * sort * tm * tm
  | Data of D.t * tms
  | Cons of C.t * tms
  | Match of tm * tm binder * cls
  (* equality *)
  | Eq of tm * tm
  | Refl
  | Rew of tm mbinder * tm * tm
  (* monadic *)
  | IO of tm
  | Return of tm
  | MLet of tm * tm binder
  (* session *)
  | Proto
  | End of role
  | Act of rel * role * tm * tm binder
  | Ch of role * tm
  | Open of prim
  | Fork of tm * tm binder
  | Recv of rel * tm
  | Send of rel * tm
  | Close of tm

and tms = tm list
and cl = PPair of rel * sort * tm mbinder | PCons of C.t * tm mbinder
and cls = cl list

type dcl = DTm of rel * id * tm * tm | DData of D.t * tm param * dconss
and dcls = dcl list
and dcons = DCons of C.t * tele param
and dconss = dcons list
and 'a param = PBase of 'a | PBind of tm * 'a param binder
and tele = TBase of tm | TBind of rel * tm * tele binder
