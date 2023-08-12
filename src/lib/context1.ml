open Fmt
open Bindlib
open Names
open Syntax1

module Ctx = struct
  type t =
    { var : (tm option * tm) Var.Map.t
    ; svar : SVar.Set.t
    ; const : (tm * tm) scheme Const.Map.t
    ; ind : (tele param scheme * Constr.t list) Ind.Map.t
    ; constr : (tele param scheme * mode) Constr.Map.t
    }

  let empty =
    { var = Var.Map.empty
    ; svar = SVar.Set.empty
    ; const = Const.Map.empty
    ; ind = Ind.Map.empty
    ; constr = Constr.Map.empty
    }

  let add_var0 x a (ctx : t) =
    { ctx with var = Var.Map.add x (None, a) ctx.var }

  let add_var1 x m a (ctx : t) =
    { ctx with var = Var.Map.add x (Some m, a) ctx.var }

  let add_svar x (ctx : t) = { ctx with svar = SVar.Set.add x ctx.svar }

  let add_const x sch (ctx : t) =
    { ctx with const = Const.Map.add x sch ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch ctx =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let find_var0 x (ctx : t) =
    try snd (Var.Map.find x ctx.var) with
    | _ -> failwith "context1.find_var0(%a)" Var.pp x

  let find_var1 x (ctx : t) : tm option =
    try fst (Var.Map.find x ctx.var) with
    | _ -> None

  let find_svar x (ctx : t) : SVar.t = SVar.Set.find x ctx.svar
  let find_const x (ctx : t) = Const.Map.find x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find x ctx.constr
  let spine_var (ctx : t) = ctx.var |> Var.Map.bindings |> List.map fst
  let spine_svar (ctx : t) = ctx.svar |> SVar.Set.elements
end

module MCtx : sig
  type t

  val empty : t
  val add_imeta : Ctx.t -> IMeta.t -> sorts -> tms -> tm -> t -> t
  val find_imeta : IMeta.t -> t -> tm option
  val entries : t -> (Ctx.t * tm * tm) list
  val pp : t Fmt.t
end = struct
  type t = (Ctx.t * sorts * tms * tm) IMeta.Map.t

  let empty = IMeta.Map.empty
  let add_imeta ctx x ss xs a (mctx : t) = IMeta.Map.add x (ctx, ss, xs, a) mctx

  let find_imeta x (mctx : t) =
    match IMeta.Map.find_opt x mctx with
    | Some (_, _, _, a) -> Some a
    | _ -> None

  let entries (mctx : t) =
    List.map
      (fun (x, (ctx, ss, xs, a)) -> (ctx, IMeta (x, ss, xs), a))
      (IMeta.Map.bindings mctx)

  let pp fmt (mctx : t) =
    let open Pprint1 in
    let rec aux fmt = function
      | [] -> ()
      | [ (x, (_, _, _, a)) ] -> pf fmt "?%a :? %a" IMeta.pp x pp_tm a
      | (x, (_, _, _, a)) :: ls ->
        pf fmt "?%a :? %a@;<1 0>%a" IMeta.pp x pp_tm a aux ls
    in
    pf fmt "@[<v 0>mctx {|@;<1 2>@[<v 0>%a@]@;<1 0>|}@]" aux
      (IMeta.Map.bindings mctx)
end
