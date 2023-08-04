open Bindlib
open Names
open Syntax1

module SVar = struct
  module Inner = struct
    open Fmt

    type t = sort var

    let mk = new_var (fun x -> SVar x)
    let compare = compare_vars
    let pp fmt x = pf fmt "%s_s%d" (name_of x) (uid_of x)
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
    let pp fmt x = pf fmt "%s_s%d" (name_of x) (uid_of x)
  end

  include Inner
  module Set = Set.Make (Inner)
  module Map = Map.Make (Inner)
end

(* smart constructors *)
let var x = Var x

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

(* core *)
let _Type = box_apply (fun s -> Type s)
let _Var = box_var
let _Const x = box_apply (fun ss -> Const (x, ss))
let _Pi relv = box_apply3 (fun s a b -> Pi (relv, s, a, b))
let _Fun = box_apply2 (fun a bnd -> Fun (a, bnd))
let _App = box_apply2 (fun m n -> App (m, n))
let _Let relv = box_apply2 (fun m n -> Let (relv, m, n))

(* inductive *)
let _Ind ind = box_apply3 (fun ss ms ns -> Ind (ind, ss, ms, ns))
let _Constr constr = box_apply3 (fun ss ms ns -> Constr (constr, ss, ms, ns))
let _Match = box_apply3 (fun ms a cls -> Match (ms, a, cls))

(* monad *)
let _IO = box_apply (fun a -> IO a)
let _Return = box_apply (fun m -> Return m)
let _MLet = box_apply2 (fun m n -> MLet (m, n))

(* magic *)
let _Magic = box_apply (fun a -> Magic a)

(* bound pattern *)
let _P0Rel = box P0Rel
let _P0Absurd = box P0Absurd
let _P0Mul constr = box_apply (fun ps -> P0Mul (constr, ps))
let _P0Add constr i = box_apply (fun ps -> P0Add (constr, i, ps))

(* dconstr *)
let _DMul constr = box_apply (fun tele -> DMul (constr, tele))
let _DAdd constr = box_apply (fun tele -> DMul (constr, tele))

(* param *)
let _PBase a = box_apply (fun a -> PBase a) a
let _PBind a b = box_apply2 (fun a b -> PBind (a, b)) a b

(* tele *)
let _TBase = box_apply (fun a -> TBase a)
let _TBind relv = box_apply2 (fun a b -> TBind (relv, a, b))

(* spine forms *)
let mkApps hd ms = List.fold_left (fun acc m -> App (acc, m)) hd ms
let _mkApps hd ms = List.fold_left _App hd ms

let rec unApps m =
  match m with
  | App (m, n) ->
    let h, ms = unApps m in
    (h, Array.append ms [| n |])
  | _ -> (m, [||])

(* box *)
let box_relv = function
  | N -> _N
  | R -> _R

let rec box_p0 = function
  | P0Rel -> _P0Rel
  | P0Absurd -> _P0Absurd
  | P0Mul (constr, ps) ->
    let ps = List.map box_p0 ps in
    _P0Mul constr (box_list ps)
  | P0Add (constr, i, ps) ->
    let ps = List.map box_p0 ps in
    _P0Add constr i (box_list ps)

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
  (* core *)
  | Type s -> _Type (lift_sort s)
  | Var x -> _Var x
  | Const (x, ss) ->
    let ss = List.map lift_sort ss in
    _Const x (box_list ss)
  | Pi (relv, s, a, bnd) ->
    _Pi relv (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | Fun (a, bnd) ->
    let bnd = box_binder (fun cls -> lift_cls cls) bnd in
    _Fun (lift_tm a) bnd
  | App (m, n) -> _App (lift_tm m) (lift_tm n)
  | Let (relv, m, bnd) -> _Let relv (lift_tm m) (box_binder lift_tm bnd)
  (* inductive *)
  | Ind (ind, ss, ms, ns) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    let ns = List.map lift_tm ns in
    _Ind ind (box_list ss) (box_list ms) (box_list ns)
  | Constr (constr, ss, ms, ns) ->
    let ss = List.map lift_sort ss in
    let ms = List.map lift_tm ms in
    let ns = List.map lift_tm ns in
    _Constr constr (box_list ss) (box_list ms) (box_list ns)
  | Match (ms, a, cls) ->
    let ms = List.map lift_tm ms in
    _Match (box_list ms) (lift_tm a) (lift_cls cls)
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

(* pattern equality *)
let rec eq_p0 p1 p2 =
  match (p1, p2) with
  | P0Rel, P0Rel -> true
  | P0Absurd, P0Absurd -> true
  | P0Mul (constr1, p0s1), P0Mul (constr2, p0s2) ->
    Constr.equal constr1 constr1 && eq_p0s p0s1 p0s2
  | P0Add (constr1, i1, p0s1), P0Add (constr2, i2, p0s2) ->
    Constr.equal constr1 constr1 && i1 = i2 && eq_p0s p0s1 p0s2
  | _ -> false

and eq_p0s ps1 ps2 = List.equal eq_p0 ps1 ps2

and eq_pbinder eq (p0s1, bnd1) (p0s2, bnd2) =
  eq_p0s p0s1 p0s2 && eq_mbinder eq bnd1 bnd2

(* pattern binding *)
let rec mvar_of_p p =
  match p with
  | PVar x -> ([ x ], P0Rel)
  | PAbsurd -> ([], P0Absurd)
  | PMul (constr, ps) ->
    let xs, p0s = mvar_of_ps ps in
    (xs, P0Mul (constr, p0s))
  | PAdd (constr, i, ps) ->
    let xs, p0s = mvar_of_ps ps in
    (xs, P0Add (constr, i, p0s))

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
  | _, P0Mul (constr, p0s) ->
    let mvar, ps = ps_of_mvar mvar p0s in
    (mvar, PMul (constr, ps))
  | _, P0Add (constr, i, p0s) ->
    let mvar, ps = ps_of_mvar mvar p0s in
    (mvar, PAdd (constr, i, ps))

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

(* pattern substitution *)
let psubst (p0s, bnd) ms =
  let rec match_p0 p0 m =
    match (p0, m) with
    | P0Rel, _ -> [ m ]
    | P0Mul (constr1, p0s), Constr (constr2, _, _, ms)
      when Constr.equal constr1 constr2 ->
      match_p0s p0s ms
    | P0Add (constr1, _, p0s), Constr (constr2, _, _, ms)
      when Constr.equal constr1 constr2 ->
      match_p0s p0s ms
    | _ -> failwith "binding1.match_p0"
  and match_p0s p0s ms =
    List.fold_left2 (fun acc p0 m -> acc @ match_p0 p0 m) [] p0s ms
  in
  let ms = match_p0s p0s ms in
  msubst bnd (Array.of_list ms)
