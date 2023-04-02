open Fmt
open Bindlib
open Names
open Syntax1
open Equality1
open Unify1
open Pprint1

type ctx =
  { (* types for variables *)
    var : tm VMap.t
  ; (* type-schemes for constants *)
    const : tm scheme VMap.t
  ; (* type-schemes for data *)
    data : (tm param scheme * CSet.t) DMap.t
  ; (* type-schemes for constructors *)
    cons : tele param scheme CMap.t
  }

let add_var x a ctx = { ctx with var = VMap.add x a ctx.var }
let add_const x sch ctx = { ctx with const = VMap.add x sch ctx.const }
let add_data d sch cs ctx = { ctx with data = DMap.add d (sch, cs) ctx.data }
let add_cons c sch ctx = { ctx with cons = CMap.add c sch ctx.cons }

let find_var x ctx =
  match VMap.find_opt x ctx.var with
  | Some a -> a
  | None -> failwith "find_var(%a)" V.pp x

let find_const x ctx =
  match VMap.find_opt x ctx.const with
  | Some sch -> sch
  | None -> failwith "find_const(%a)" V.pp x

let find_data d ctx =
  match DMap.find_opt d ctx.data with
  | Some res -> res
  | None -> failwith "find_data(%a)" D.pp d

let find_cons c ctx =
  match CMap.find_opt c ctx.cons with
  | Some sch -> sch
  | None -> failwith "find_cons(%a)" C.pp c

let meta_mk ctx =
  let x = M.mk () in
  let xs = ctx.var |> VMap.bindings |> List.map (fun x -> Var (fst x)) in
  (Meta (x, xs), x)

type 'a trans1e = eqns * map0 * map1 -> 'a * eqns * map0 * map1
