open Fmt
open Bindlib
open Names
open Syntax1
open Pprint1

module Ctx = struct
  type t =
    { var : tm Var.Map.t
    ; svar : SVar.Set.t
    ; const : tm scheme Const.Map.t
    ; ind : (tele param scheme * Constr.t list) Ind.Map.t
    ; constr : tele param scheme Constr.Map.t
    }

  let empty =
    { var = Var.Map.empty
    ; svar = SVar.Set.empty
    ; const = Const.Map.empty
    ; ind = Ind.Map.empty
    ; constr = Constr.Map.empty
    }

  let add_var x a (ctx : t) = { ctx with var = Var.Map.add x a ctx.var }
  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch ctx =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let find_var x (ctx : t) =
    try Var.Map.find x ctx.var with
    | _ -> failwith "context1e.Ctx.find_var(%a)" Var.pp x

  let find_svar x (ctx : t) : SVar.t =
    try SVar.Set.find x ctx.svar with
    | _ -> failwith "context1e.Ctx.find_svar(%a)" SVar.pp x

  let find_const x (ctx : t) =
    try Const.Map.find x ctx.const with
    | _ -> failwith "context1e.Ctx.find_const(%a)" Const.pp x

  let find_ind x (ctx : t) =
    try Ind.Map.find x ctx.ind with
    | _ -> failwith "context1e.Ctx.find_ind(%a)" Ind.pp x

  let find_constr x (ctx : t) =
    try Constr.Map.find x ctx.constr with
    | _ -> failwith "context1e.Ctx.find_constr(%a)" Constr.pp x

  let spine_var (ctx : t) = ctx.var |> Var.Map.bindings |> List.map fst
  let spine_svar (ctx : t) = ctx.svar |> SVar.Set.elements

  let map_var f (ctx : t) =
    let var = Var.Map.map (fun a -> f a) ctx.var in
    { ctx with var }
end

module Env = struct
  type t =
    { var : tm Var.Map.t
    ; const : tm scheme Const.Map.t
    }

  let empty = { var = Var.Map.empty; const = Const.Map.empty }
  let add_var x m (env : t) = { env with var = Var.Map.add x m env.var }

  let add_const x sch (env : t) =
    { env with const = Const.Map.add x sch env.const }

  let find_var x (env : t) =
    try Var.Map.find x env.var with
    | _ -> failwith "context1e.Env.find_var(%a)" Var.pp x

  let find_const x (env : t) =
    try Const.Map.find x env.const with
    | _ -> failwith "context1e.Env.find_const(%a)" Const.pp x

  let merge_var var_map env =
    let var =
      Var.Map.merge
        (fun x opt1 opt2 ->
          match (opt1, opt2) with
          | Some m, None -> Some m
          | None, Some m -> Some m
          | None, None -> None
          | _ -> failwith "context1e.Env.merge_var(%a)" Var.pp x)
        var_map env.var
    in
    { env with var }

  let map_var f env =
    let var = Var.Map.map (fun a -> f a) env.var in
    { env with var }

  let pp_var fmt env =
    let aux_var fmt map =
      Var.Map.iter
        (fun x m -> pf fmt "@[%a := %a@]@;<1 0>" Var.pp x pp_tm m)
        map
    in
    pf fmt "@[<v 0>env {|@;<1 2>%a@;<1 0>|}@]" aux_var env.var
end

module MCtx : sig
  type t

  val empty : t

  val add_imeta :
    Ctx.t -> Env.t -> IMeta.t -> sorts box -> tms box -> tm -> t -> t

  val find_imeta : IMeta.t -> t -> (sorts box * tms box * tm) option
  val entries : t -> (Ctx.t * Env.t * tm * tm) list
  val pp : t Fmt.t
end = struct
  type t = (Ctx.t * Env.t * sorts box * tms box * tm) IMeta.Map.t

  let empty = IMeta.Map.empty

  let add_imeta ctx env x ss xs a (mctx : t) =
    IMeta.Map.add x (ctx, env, ss, xs, a) mctx

  let find_imeta x (mctx : t) =
    match IMeta.Map.find_opt x mctx with
    | Some (_, _, ss, ms, a) -> Some (ss, ms, a)
    | _ -> None

  let entries (mctx : t) =
    List.map
      (fun (x, (ctx, env, ss, xs, a)) ->
        (ctx, env, IMeta (x, unbox ss, unbox xs), a))
      (IMeta.Map.bindings mctx)

  let pp fmt (mctx : t) =
    let open Pprint1 in
    let rec aux fmt = function
      | [] -> ()
      | [ (x, (_, _, _, _, a)) ] -> pf fmt "?%a :? %a" IMeta.pp x pp_tm a
      | (x, (_, _, _, _, a)) :: ls ->
        pf fmt "?%a :? %a@;<1 0>%a" IMeta.pp x pp_tm a aux ls
    in
    pf fmt "@[<v 0>mctx {|@;<1 2>@[<v 0>%a@]@;<1 0>|}@]" aux
      (IMeta.Map.bindings mctx)
end
