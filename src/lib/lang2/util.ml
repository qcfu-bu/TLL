open Bindlib
open Names
open Syntax

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

(* spine forms *)
let mkApps h ms = Array.fold_left (fun acc m -> App (acc, m)) h ms

let rec unApps m =
  match m with
  | App (m, n) ->
    let h, ms = unApps m in
    (h, Array.append ms [| n |])
  | _ -> (m, [||])

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
let _TMeta x = box_apply2 (fun ss ms -> TMeta (x, ss, ms))

(* core *)
let _Type = box_apply (fun s -> Type s)
let _Var = box_var
let _Const x = box_apply (fun ss -> Const (x, ss))
let _Pi relv = box_apply3 (fun s a b -> Pi (relv, s, a, b))
let _Fun = box_apply2 (fun a bnd -> Fun (a, bnd))
let _App = box_apply2 (fun m n -> App (m, n))
let _Let relv = box_apply2 (fun m n -> Let (relv, m, n))

(* inductive *)
let _Ind ind = box_apply (fun ss -> Ind (ind, ss))
let _Constr constr = box_apply (fun ss -> Constr (constr, ss))
let _Absurd = box Absurd
let _Match = box_apply3 (fun ms a cls -> Match (ms, a, cls))

(* record *)
let _Record record = box_apply (fun ss -> Record (record, ss))
let _Struct = box_apply2 (fun s fields -> Struct (s, fields))
let _Proj field = box_apply (fun m -> Proj (field, m))

(* magic *)
let _Magic = box Magic

(* bound pattern *)
let _P0Rel = box P0Rel
let _P0Constr constr = box_apply (fun ps -> P0Constr (constr, ps))

(* box *)
let box_relv = function
  | N -> _N
  | R -> _R

let rec box_p0 = function
  | P0Rel -> _P0Rel
  | P0Constr (constr, ps) ->
    let ps = Array.map box_p0 ps in
    _P0Constr constr (box_array ps)

(* lifting *)
let rec lift_sort = function
  | U -> _U
  | L -> _L
  | SVar x -> _SVar x
  | SMeta (x, ss) ->
    let ss = Array.map lift_sort ss in
    _SMeta x (box_array ss)

let rec lift_tm = function
  (* inference *)
  | Ann (m, a) -> _Ann (lift_tm m) (lift_tm a)
  | IMeta (x, ss, ms) ->
    let ss = Array.map lift_sort ss in
    let ms = Array.map lift_tm ms in
    _IMeta x (box_array ss) (box_array ms)
  | TMeta (x, ss, ms) ->
    let ss = Array.map lift_sort ss in
    let ms = Array.map lift_tm ms in
    _TMeta x (box_array ss) (box_array ms)
  (* core *)
  | Type s -> _Type (lift_sort s)
  | Var x -> _Var x
  | Const (x, ss) ->
    let ss = Array.map lift_sort ss in
    _Const x (box_array ss)
  | Pi (relv, s, a, bnd) ->
    _Pi relv (lift_sort s) (lift_tm a) (box_binder lift_tm bnd)
  | Fun (a, bnd) ->
    let bnd = box_binder (fun cls -> lift_cls cls) bnd in
    _Fun (lift_tm a) bnd
  | App (m, n) -> _App (lift_tm m) (lift_tm n)
  | Let (relv, m, bnd) -> _Let relv (lift_tm m) (box_binder lift_tm bnd)
  (* inductive *)
  | Ind (ind, ss) ->
    let ss = Array.map lift_sort ss in
    _Ind ind (box_array ss)
  | Constr (constr, ss) ->
    let ss = Array.map lift_sort ss in
    _Constr constr (box_array ss)
  | Match (ms, a, cls) ->
    let ms = Array.map lift_tm ms in
    _Match (box_array ms) (lift_tm a) (lift_cls cls)
  | Absurd -> _Absurd
  (* record *)
  | Record (record, ss) ->
    let ss = Array.map lift_sort ss in
    _Record record (box_array ss)
  | Struct (a, fields) ->
    let fields =
      Array.map
        (fun (field, relv, m) ->
          box_triple (box field) (box_relv relv) (lift_tm m))
        fields
    in
    _Struct (lift_tm a) (box_array fields)
  | Proj (field, m) -> _Proj field (lift_tm m)
  (* magic *)
  | Magic -> _Magic

and lift_cls cls =
  let cls =
    Array.map
      (fun (p0s, mbnd) ->
        let p0s = Array.map box_p0 p0s in
        let mbnd = box_mbinder lift_tm mbnd in
        box_pair (box_array p0s) mbnd)
      cls
  in
  box_array cls

(* pattern equality *)
let rec eq_p0 p1 p2 =
  match (p1, p2) with
  | P0Rel, P0Rel -> true
  | P0Constr (constr1, p0s1), P0Constr (constr2, p0s2) ->
    Constr.equal constr1 constr1 && eq_p0s p0s1 p0s2
  | _ -> false

and eq_p0s ps1 ps2 = Array.for_all2 eq_p0 ps1 ps2

and eq_pbinder eq (p0s1, bnd1) (p0s2, bnd2) =
  eq_p0s p0s1 p0s2 && eq_mbinder eq bnd1 bnd2

(* pattern binding *)
let rec mvar_of_p p =
  match p with
  | PVar x -> ([| x |], P0Rel)
  | PConstr (constr, ps) ->
    let xs, p0s = mvar_of_ps ps in
    (xs, P0Constr (constr, p0s))

and mvar_of_ps ps =
  Array.fold_left_map
    (fun acc p ->
      let xs, p0 = mvar_of_p p in
      (Array.append acc xs, p0))
    [||] ps

let rec p_of_mvar mvar p0 =
  match p0 with
  | P0Rel ->
    let x = mvar.(0) in
    let mvar = Array.(sub mvar 1 (length mvar - 1)) in
    (mvar, PVar x)
  | P0Constr (constr, p0s) ->
    let mvar, p0s = ps_of_mvar mvar p0s in
    (mvar, PConstr (constr, p0s))

and ps_of_mvar mvar p0s = Array.fold_left_map p_of_mvar mvar p0s

let bind_ps ps m =
  let xs, p0s = mvar_of_ps ps in
  let bnd = bind_mvar xs m in
  box_apply (fun bnd -> (p0s, bnd)) bnd

let unbind_ps (p0s, bnd) =
  let xs, m = unmbind bnd in
  let _, ps = ps_of_mvar xs p0s in
  (ps, m)

let unbind_ps2 (p0s1, bnd1) (p0s2, bnd2) =
  assert (eq_p0s p0s1 p0s2);
  let xs, m1, m2 = unmbind2 bnd1 bnd2 in
  let _, ps = ps_of_mvar xs p0s1 in
  (ps, m1, m2)

(* pattern substitution *)
let psubst (p0s, bnd) ms =
  let rec match_p0 p0 m =
    match (p0, unApps m) with
    | P0Rel, _ -> [| m |]
    | P0Constr (constr1, p0s), (Constr (constr2, _), ms)
      when Constr.equal constr1 constr2 ->
      match_p0s p0s ms
    | _ -> failwith "match_p0"
  and match_p0s p0s ms =
    Array.fold_left
      (fun acc (p0, m) -> Array.append acc (match_p0 p0 m))
      [||] (Array.combine p0s ms)
  in
  let sz_p0s = Array.length p0s in
  let sz_ms = Array.length ms in
  if sz_p0s <= sz_ms then
    let ns = Array.sub ms 0 sz_p0s in
    let ms = Array.sub ms sz_p0s (sz_ms - sz_p0s) in
    let ns = match_p0s p0s ns in
    (msubst bnd ns, ms)
  else
    failwith "match_psubst"
