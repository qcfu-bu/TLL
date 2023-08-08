open Fmt
open Bindlib
open Names
open Syntax1

module Ctx : sig
  type t

  val empty : t
  val add_var0 : Var.t -> tm -> t -> t
  val add_var1 : Var.t -> tm -> tm -> t -> t
  val add_svar : SVar.t -> t -> t
  val add_const : Const.t -> (tm * tm) scheme -> t -> t
  val add_ind : Ind.t -> tele param scheme * Constr.Set.t -> t -> t
  val add_constr : Constr.t -> mode * tele param scheme -> t -> t
  val find_var0 : Var.t -> t -> tm option
  val find_var1 : Var.t -> t -> tm option
  val find_svar : SVar.t -> t -> SVar.t option
  val find_const : Const.t -> t -> (tm * tm) scheme option
  val find_ind : Ind.t -> t -> (tele param scheme * Constr.Set.t) option
  val find_constr : Constr.t -> t -> (mode * tele param scheme) option
  val spine_var : t -> Var.t list
  val spine_svar : t -> SVar.t list
end = struct
  type t =
    { var : (tm option * tm) Var.Map.t
    ; svar : SVar.Set.t
    ; const : (tm * tm) scheme Const.Map.t
    ; ind : (tele param scheme * Constr.Set.t) Ind.Map.t
    ; constr : (mode * tele param scheme) Constr.Map.t
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
    match Var.Map.find_opt x ctx.var with
    | Some (_, a) -> Some a
    | _ -> None

  let find_var1 x (ctx : t) : tm option =
    match Var.Map.find_opt x ctx.var with
    | Some (Some m, _) -> Some m
    | _ -> None

  let find_svar x (ctx : t) : SVar.t option = SVar.Set.find_opt x ctx.svar
  let find_const x (ctx : t) = Const.Map.find_opt x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find_opt x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find_opt x ctx.constr
  let spine_var (ctx : t) = ctx.var |> Var.Map.bindings |> List.map fst
  let spine_svar (ctx : t) = ctx.svar |> SVar.Set.elements
end

module MCtx : sig
  type t

  val empty : t
  val add_imeta : Ctx.t -> IMeta.t -> tm -> t -> t
  val find_imeta : IMeta.t -> t -> tm option
  val pp : t Fmt.t
end = struct
  type t = (Ctx.t * tm) IMeta.Map.t

  let empty = IMeta.Map.empty
  let add_imeta ctx x a (mctx : t) = IMeta.Map.add x (ctx, a) mctx

  let find_imeta x (mctx : t) =
    match IMeta.Map.find_opt x mctx with
    | Some (_, a) -> Some a
    | _ -> None

  let pp fmt mctx =
    let open Pprint1 in
    let rec aux fmt = function
      | [] -> ()
      | [ (x, (_, a)) ] -> pf fmt "?%a :? %a" IMeta.pp x pp_tm a
      | (x, (_, a)) :: ls ->
        pf fmt "?%a :? %a@;<1 0>%a" IMeta.pp x pp_tm a aux ls
    in
    aux fmt (IMeta.Map.bindings mctx)
end
