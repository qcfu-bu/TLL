open Bindlib
open Names

(* sorts *)
type sort =
  | U
  | L
  | SVar of sort var
  | SMeta of SMeta.t * sorts

and sorts = sort list

(* relevancy *)
type relv =
  | N
  | R

(* terms *)
type tm =
  (* inference *)
  | Ann of tm * tm
  | IMeta of IMeta.t * sorts * tms
  | PMeta of tm var
  (* core *)
  | Type of sort
  | Var of tm var
  | Const of Const.t * sorts
  | TName of TName.t * sorts
  | Pi of relv * sort * tm * (tm, tm) binder
  | Fun of guard * tm * (tm, cls) binder
  | App of tm * tm
  | Let of relv * tm * (tm, tm) binder
  (* inductive *)
  | Ind of Ind.t * sorts * tms * tms
  | Constr of Constr.t * sorts * tms * tms
  | Match of guard * tms * tm * cls
  (* monad *)
  | IO of tm
  | Return of tm
  | MLet of tm * (tm, tm) binder
  (* magic *)
  | Magic of tm

and tms = tm list

(* unbound pattern *)
and p =
  | PVar of tm var
  | PAbsurd
  | PConstr of Constr.t * ps

and ps = p list

(* bound pattern *)
and p0 =
  | P0Rel
  | P0Absurd
  | P0Constr of Constr.t * p0s

and p0s = p0 list

(* clause *)
and cl = p0s * (tm, tm option) mbinder
and cls = cl list
and guard = bool list

(* declarations *)
type dcl =
  | Definition of
      { name : Const.t
      ; relv : relv
      ; scheme : (tm * tm) scheme
      }
  | Inductive of
      { name : Ind.t
      ; relv : relv
      ; arity : tele param scheme
      ; dconstrs : dconstrs
      }
  | Template of
      { name : TName.t
      ; relv : relv
      ; scheme : tm scheme
      }
  | Implement of 
      { name : Const.t
      ; relv : relv
      ; tmpl : TName.t
      ; scheme : (tm * tm) scheme
      }
  | Extern of
      { name : Const.t
      ; relv : relv
      ; scheme : (tm option * tm) scheme
      }

and dcls = dcl list
and dconstr = Constr.t * tele param scheme
and dconstrs = dconstr list
and 'a scheme = (sort, 'a) mbinder

and 'a param =
  | PBase of 'a
  | PBind of tm * (tm, 'a param) binder

and tele =
  | TBase of tm
  | TBind of relv * tm * (tm, tele) binder

(* utility *)
module SVar = struct
  module Inner = struct
    open Fmt

    type t = sort var

    let mk = new_var (fun x -> SVar x)
    let compare = compare_vars
    let pp fmt x = pf fmt "%s_%d" (name_of x) (uid_of x)
  end

  include Inner
  module Set = Set.Make (Inner)
  module Map = Map.Make (Inner)
end

module Var = struct
  module Inner = struct
    open Fmt

    type t = tm var

    let mk = new_var (fun x -> Var x)
    let compare = compare_vars
    let pp fmt x = pf fmt "%s_%d" (name_of x) (uid_of x)
  end

  include Inner
  module Set = Set.Make (Inner)
  module Map = Map.Make (Inner)
end

(* smart constructors *)
let var x = Var x
let svar x = SVar x

(* option *)
let _Some m = box_apply (fun m -> Some m) m
let _None = box None

(* sort *)
let _U = box U
let _L = box L
let _SVar = box_var
let _SMeta x = box_apply (fun ss -> SMeta (x, ss))

(* relv *)
let _N = box N
let _R = box R

(* inference *)
let _Ann = box_apply2 (fun m a -> Ann (m, a))
let _IMeta x = box_apply2 (fun ss ms -> IMeta (x, ss, ms))
let _PMeta x = box (PMeta x)

(* core *)
let _Type = box_apply (fun s -> Type s)
let _Var = box_var
let _Const x = box_apply (fun ss -> Const (x, ss))
let _Pi relv = box_apply3 (fun s a b -> Pi (relv, s, a, b))
let _Fun guard = box_apply2 (fun a bnd -> Fun (guard, a, bnd))
let _App = box_apply2 (fun m n -> App (m, n))
let _Let relv = box_apply2 (fun m n -> Let (relv, m, n))

(* inductive *)
let _Ind d = box_apply3 (fun ss ms ns -> Ind (d, ss, ms, ns))
let _Constr c = box_apply3 (fun ss ms ns -> Constr (c, ss, ms, ns))
let _Match guard = box_apply3 (fun ms a cls -> Match (guard, ms, a, cls))

(* monad *)
let _IO = box_apply (fun a -> IO a)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m n -> MLet (m, n))

(* magic *)
let _Magic = box_apply (fun a -> Magic a)

(* bound pattern *)
let _P0Rel = box P0Rel
let _P0Absurd = box P0Absurd
let _P0Constr c = box_apply (fun ps -> P0Constr (c, ps))

(* dconstr *)
let _DConstr c = box_apply (fun sch -> (c, sch))

(* param *)
let _PBase a = box_apply (fun a -> PBase a) a
let _PBind a b = box_apply2 (fun a b -> PBind (a, b)) a b

(* tele *)
let _TBase = box_apply (fun a -> TBase a)
let _TBind relv = box_apply2 (fun a b -> TBind (relv, a, b))

(* spine forms *)
let mkApps hd ms = List.fold_left (fun acc m -> App (acc, m)) hd ms
let _mkApps hd ms = List.fold_left _App hd ms

let unApps m =
  let rec aux m ns =
    match m with
    | App (m, n) -> aux m (n :: ns)
    | _ -> (m, ns)
  in
  aux m []

(* box *)
let box_relv = function
  | N -> _N
  | R -> _R

let rec box_p0 = function
  | P0Rel -> _P0Rel
  | P0Absurd -> _P0Absurd
  | P0Constr (c, ps) ->
    let ps = List.map box_p0 ps in
    _P0Constr c (box_list ps)

(* lifting *)
let rec lift_sort = function
  | U -> _U
  | L -> _L
  | SVar x -> _SVar x
  | SMeta (x, ss) ->
    let ss = List.map lift_sort ss in
    _SMeta x (box_list ss)

let rec lift_tm = function
  (* inference *)
  | Ann (m, a) -> _Ann (lift_tm m) (lift_tm a)
  | IMeta (x, ss, ms) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    _IMeta x (box_list ss) (box_list ms)
  | PMeta x -> _PMeta x
  (* core *)
  | Type s -> _Type (lift_sort s)
  | Var x -> _Var x
  | Const (x, ss) ->
    let ss = List.map lift_sort ss in
    _Const x (box_list ss)
  | Pi (relv, s, a, bnd) ->
    _Pi relv (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | Fun (guard, a, bnd) ->
    let bnd = box_binder (fun cls -> lift_cls cls) bnd in
    _Fun guard (lift_tm a) bnd
  | App (m, n) -> _App (lift_tm m) (lift_tm n)
  | Let (relv, m, bnd) -> _Let relv (lift_tm m) (box_binder lift_tm bnd)
  (* inductive *)
  | Ind (d, ss, ms, ns) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    let ns = List.map lift_tm ns in
    _Ind d (box_list ss) (box_list ms) (box_list ns)
  | Constr (c, ss, ms, ns) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    let ns = List.map lift_tm ns in
    _Constr c (box_list ss) (box_list ms) (box_list ns)
  | Match (guard, ms, a, cls) ->
    let ms = List.map lift_tm ms in
    _Match guard (box_list ms) (lift_tm a) (lift_cls cls)
  (* monad *)
  | IO a -> _IO (lift_tm a)
  | Return m -> _Return (lift_tm m)
  | MLet (m, bnd) -> _MLet (lift_tm m) (box_binder lift_tm bnd)
  (* magic *)
  | Magic a -> _Magic (lift_tm a)

and lift_cls cls =
  let cls =
    List.map
      (fun (p0s, mbnd) ->
        let p0s = List.map box_p0 p0s in
        let mbnd =
          box_mbinder (fun opt -> opt |> Option.map lift_tm |> box_opt) mbnd
        in
        box_pair (box_list p0s) mbnd)
      cls
  in
  box_list cls

let rec lift_param lift = function
  | PBase a -> _PBase (lift a)
  | PBind (a, bnd) -> _PBind (lift_tm a) (box_binder (lift_param lift) bnd)

let rec lift_tele = function
  | TBase a -> _TBase (lift_tm a)
  | TBind (relv, a, bnd) -> _TBind relv (lift_tm a) (box_binder lift_tele bnd)

(* sort equality *)
let rec eq_sort s1 s2 =
  match (s1, s2) with
  | SVar x, SVar y -> eq_vars x y
  | SMeta (x1, _), SMeta (x2, _) -> SMeta.equal x1 x2
  | _ -> s1 = s2

(* pattern equality *)
let rec eq_p0 p1 p2 =
  match (p1, p2) with
  | P0Rel, P0Rel -> true
  | P0Absurd, P0Absurd -> true
  | P0Constr (c1, p0s1), P0Constr (c2, p0s2) ->
    Constr.equal c1 c2 && eq_p0s p0s1 p0s2
  | _ -> false

and eq_p0s ps1 ps2 = List.equal eq_p0 ps1 ps2

and eq_pbinder eq (p0s1, bnd1) (p0s2, bnd2) =
  eq_p0s p0s1 p0s2 && eq_mbinder eq bnd1 bnd2

(* pattern binding *)
let rec mvar_of_p p =
  match p with
  | PVar x -> ([ x ], P0Rel)
  | PAbsurd -> ([], P0Absurd)
  | PConstr (c, ps) ->
    let xs, p0s = mvar_of_ps ps in
    (xs, P0Constr (c, p0s))

and mvar_of_ps ps =
  List.fold_left_map
    (fun acc p ->
      let xs, p0 = mvar_of_p p in
      (acc @ xs, p0))
    [] ps

let rec p_of_mvar mvar p0 =
  match (mvar, p0) with
  | [], P0Rel -> failwith "binding1.p_of_mvar"
  | x :: mvar, P0Rel -> (mvar, PVar x)
  | _, P0Absurd -> (mvar, PAbsurd)
  | _, P0Constr (c, p0s) ->
    let mvar, ps = ps_of_mvar mvar p0s in
    (mvar, PConstr (c, ps))

and ps_of_mvar mvar p0s = List.fold_left_map p_of_mvar mvar p0s

let bind_ps ps m =
  let xs, p0s = mvar_of_ps ps in
  let bnd = bind_mvar (Array.of_list xs) m in
  box_apply (fun bnd -> (p0s, bnd)) bnd

let unbind_ps (p0s, bnd) =
  let xs, m = unmbind bnd in
  let _, ps = ps_of_mvar (Array.to_list xs) p0s in
  (ps, m)

let unbind_ps2 (p0s1, bnd1) (p0s2, bnd2) =
  assert (eq_p0s p0s1 p0s2);
  let xs, m1, m2 = unmbind2 bnd1 bnd2 in
  let _, ps = ps_of_mvar (Array.to_list xs) p0s1 in
  (ps, m1, m2)

let unbind_pmeta bnd =
  let s = binder_name bnd in
  let x = Var.mk s in
  (x, subst bnd (PMeta x))

let unmbind_pmeta bnd =
  let ss = mbinder_names bnd in
  let xs = Array.map Var.mk ss in
  let ms = Array.map (fun x -> PMeta x) xs in
  (xs, msubst bnd ms)

(* pattern substitution *)
let psubst (p0s, bnd) ms =
  let rec match_p0 p0 m =
    match (p0, m) with
    | P0Rel, _ -> [ m ]
    | P0Constr (c1, p0s), Constr (c2, _, _, ms) when Constr.equal c1 c2 ->
      match_p0s p0s ms
    | _ -> failwith "binding1.match_p0"
  and match_p0s p0s ms =
    List.fold_left2 (fun acc p0 m -> acc @ match_p0 p0 m) [] p0s ms
  in
  let ms = match_p0s p0s ms in
  msubst bnd (Array.of_list ms)

(* pattern expansion *)
let expand_ps ps pvar_map =
  let rec aux_p = function
    | PVar x -> (
      match Var.Map.find_opt x pvar_map with
      | Some p -> aux_p p
      | None -> PVar x)
    | PAbsurd -> PAbsurd
    | PConstr (c, ps) -> PConstr (c, aux_ps ps)
  and aux_ps ps = List.map aux_p ps in
  aux_ps ps

(* param instantiation *)
let rec param_inst param ms =
  match (param, ms) with
  | PBase a, [] -> a
  | PBind (_, bnd), m :: ms -> param_inst (subst bnd m) ms
  | _ -> failwith "syntax1.param_inst"

let rec unbind_tele = function
  | TBase a -> ([], a)
  | TBind (relv, a, bnd) ->
    let x, tele = unbind_pmeta bnd in
    let args, b = unbind_tele tele in
    ((relv, x, a) :: args, b)
