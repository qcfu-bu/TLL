open Fmt
open Bindlib
open Names
open Syntax1
open Pprint1

module Ctx = struct
  type t =
    { var : (tm * sort) Var.Map.t
    ; const : (tm * sort) Const.Map.t
    ; ind : (tele param * Constr.t list) Ind.Map.t
    ; constr : (tele param * relv * mode) Constr.Map.t
    }

  let empty =
    { var = Var.Map.empty
    ; const = Const.Map.empty
    ; ind = Ind.Map.empty
    ; constr = Constr.Map.empty
    }

  let add_var x a s (ctx : t) = { ctx with var = Var.Map.add x (a, s) ctx.var }

  let add_const x a s (ctx : t) =
    { ctx with const = Const.Map.add x (a, s) ctx.const }

  let add_ind x ind (ctx : t) = { ctx with ind = Ind.Map.add x ind ctx.ind }

  let add_constr x sch ctx =
    { ctx with constr = Constr.Map.add x sch ctx.constr }

  let find_var x (ctx : t) =
    try Var.Map.find x ctx.var with
    | _ -> failwith "context1.find_var0(%a)" Var.pp x

  let find_const x (ctx : t) = Const.Map.find x ctx.const
  let find_ind x (ctx : t) = Ind.Map.find x ctx.ind
  let find_constr x (ctx : t) = Constr.Map.find x ctx.constr

  let map_var f (ctx : t) : t =
    let var = Var.Map.map (fun (a, s) -> (f a, s)) ctx.var in
    { ctx with var }
end

module Env = struct
  type t =
    { var : tm Var.Map.t
    ; const : (sorts -> tm) Const.Map.t
    }

  let empty = { var = Var.Map.empty; const = Const.Map.empty }
  let find_var x env = Var.Map.find_opt x env.var
  let find_const x env = Const.Map.find_opt x env.const
  let add_var x m env = { env with var = Var.Map.add x m env.var }

  let add_const x entry env =
    { env with const = Const.Map.add x entry env.const }
end

module Resolver = struct
  module Sorts = struct
    type t = sorts

    let compare ss1 ss2 = List.compare (fun s1 s2 -> compare s1 s2) ss1 ss2
  end

  module RMap = Map.Make (Sorts)

  type t =
    { const : Const.t RMap.t Const.Map.t
    ; ind : Ind.t RMap.t Ind.Map.t
    ; constr : Constr.t RMap.t Constr.Map.t
    }

  let empty =
    { const = Const.Map.empty; ind = Ind.Map.empty; constr = Constr.Map.empty }

  let add_const x0 rmap (res : t) =
    { res with const = Const.Map.add x0 rmap res.const }

  let add_ind d0 ss d1 (res : t) : t =
    { res with
      ind =
        Ind.Map.add d0
          (match Ind.Map.find_opt d0 res.ind with
          | Some rmap -> RMap.add ss d1 rmap
          | None -> RMap.singleton ss d1)
          res.ind
    }

  let add_constr c0 ss c1 (res : t) : t =
    { res with
      constr =
        Constr.Map.add c0
          (match Constr.Map.find_opt c0 res.constr with
          | Some rmap -> RMap.add ss c1 rmap
          | None -> RMap.singleton ss c1)
          res.constr
    }

  let find_const x0 ss (res : t) : Const.t =
    match Const.Map.find_opt x0 res.const with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some x1 -> x1
      | None -> failwith "context12.Resolver.find_const(%a)" Const.pp x0)
    | None -> failwith "context12.Resolver.find_const(%a)" Const.pp x0

  let find_ind d0 ss (res : t) : Ind.t =
    match Ind.Map.find_opt d0 res.ind with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some d1 -> d1
      | None -> failwith "context12.Resolver.find_ind(%a)" Ind.pp d0)
    | None -> failwith "context12.Resolver.find_ind(%a)" Ind.pp d0

  let find_constr c0 ss (res : t) : Constr.t =
    match Constr.Map.find_opt c0 res.constr with
    | Some rmap -> (
      match RMap.find_opt ss rmap with
      | Some d1 -> d1
      | None -> failwith "context12.Resolver.find_constr(%a)" Constr.pp c0)
    | None -> failwith "context12.Resolver.find_constr(%a)" Constr.pp c0
end

module Usage = struct
  type t =
    { (* true: slacked usage, false: fixed usage *)
      var : (sort * bool) Var.Map.t
    ; const : (sort * bool) Const.Map.t
    }

  let empty = { var = Var.Map.empty; const = Const.Map.empty }

  let var_singleton x entry =
    { var = Var.Map.singleton x entry; const = Const.Map.empty }

  let const_singleton x entry =
    { var = Var.Map.empty; const = Const.Map.singleton x entry }

  let merge usg1 usg2 =
    let aux _ opt1 opt2 =
      match (opt1, opt2) with
      | Some (L, false), Some (_, false) -> failwith "merge"
      | Some (_, false), Some (L, false) -> failwith "merge"
      | Some (s1, b1), Some (s2, b2) ->
        if eq_sort s1 s2 then
          Some (s1, b1 && b2)
        else
          failwith "merge"
      | Some b, None -> Some b
      | None, Some b -> Some b
      | _ -> None
    in
    { var = Var.Map.merge aux usg1.var usg2.var
    ; const = Const.Map.merge aux usg1.const usg2.const
    }

  let refine_usage usg1 usg2 =
    let aux _ opt1 opt2 =
      match (opt1, opt2) with
      | Some (U, false), None -> Some (U, false)
      | None, Some (U, false) -> Some (U, false)
      | Some (s1, b1), Some (s2, b2) when eq_sort s1 s2 -> Some (s1, b1 && b2)
      | Some (_, true), None -> None
      | None, Some (_, true) -> None
      | None, None -> None
      | _ -> failwith "refine_usage"
    in
    { var = Var.Map.merge aux usg1.var usg2.var
    ; const = Const.Map.merge aux usg1.const usg2.const
    }

  let refine_pure usg =
    let var =
      Var.Map.filter_map
        (fun x (sort, slack) ->
          match (sort, slack) with
          | U, _ -> Some (U, slack)
          | L, true -> None
          | _ -> failwith "refine_pure(Var %a)" Var.pp x)
        usg.var
    in
    let const =
      Const.Map.filter_map
        (fun x (sort, slack) ->
          match (sort, slack) with
          | U, _ -> Some (U, slack)
          | L, true -> None
          | _ -> failwith "refine_pure(Const %a)" Const.pp x)
        usg.const
    in
    { var; const }

  let assert_empty usg =
    let aux _ (_, b) = b in
    if Var.Map.for_all aux usg.var && Const.Map.for_all aux usg.const then
      ()
    else
      let aux0 fmt map =
        Var.Map.iter
          (fun x (s, b) -> pf fmt "{%a, %a, %b}@." Var.pp x pp_sort s b)
          map
      in
      let aux1 fmt map =
        Const.Map.iter
          (fun x (s, b) -> pf fmt "{%a, %a, %b}@." Const.pp x pp_sort s b)
          map
      in
      failwith "assert_empty@.%a@.%a" aux0 usg.var aux1 usg.const

  let remove_var x usg r s =
    match (r, s) with
    | N, _ ->
      if Var.Map.exists (fun y (_, b) -> eq_vars x y && not b) usg.var then
        failwith "remove_var(%a)" Var.pp x
      else
        { usg with var = Var.Map.remove x usg.var }
    | R, U -> { usg with var = Var.Map.remove x usg.var }
    | R, L ->
      if Var.Map.exists (fun y _ -> eq_vars x y) usg.var then
        { usg with var = Var.Map.remove x usg.var }
      else
        failwith "remove_var(%a)" Var.pp x
    | _ -> failwith "remove_var(%a)" Var.pp x

  let remove_const x usg r s =
    match (r, s) with
    | N, _ ->
      if Const.Map.exists (fun y (_, b) -> Const.equal x y && not b) usg.const
      then
        failwith "remove_const(%a)" Const.pp x
      else
        { usg with const = Const.Map.remove x usg.const }
    | R, U -> { usg with const = Const.Map.remove x usg.const }
    | R, L ->
      if Const.Map.exists (fun y _ -> Const.equal x y) usg.const then
        { usg with const = Const.Map.remove x usg.const }
      else
        failwith "remove_const(%a)" Const.pp x
    | _ -> failwith "remove_const(%a)" Const.pp x

  let of_ctx (ctx : Ctx.t) =
    { var = Var.Map.map (fun (_, s) -> (s, true)) ctx.var
    ; const = Const.Map.map (fun (_, s) -> (s, true)) ctx.const
    }
end
