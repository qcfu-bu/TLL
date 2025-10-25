open Fmt
open Names
open Syntax4

(* module Vtbl = struct *)
(*   type t = Syntax5.expr Name.Map.t *)

(*   let empty : t = Name.Map.empty *)
(*   let singleton x e : t = Name.Map.singleton x e *)
(*   let of_names xs : t = *)
(*     List.fold_left (fun acc x -> Name.Map.add x (Syntax5.Var x) acc) empty xs *)
(*   let fold_names f (vtbl : t) xs : t =  *)
(*     snd @@ List.fold_left (fun (i, acc) x -> *)
(*         (i + 1, f i acc x)) *)
(*       (0, vtbl) xs *)

(*   let find x (vtbl : t) = *)
(*     try Name.Map.find x vtbl *)
(*     with _ -> failwith "Vtbl.find_name(%a)" Name.pp x *)

(*   let add x m (vtbl : t) : t = Name.Map.add x m vtbl *)
(* end *)

module Fv = struct
  type t = Name.Set.t

  let empty : t = Name.Set.empty
  let singleton x : t = Name.Set.singleton x
  let of_list xs : t = Name.Set.of_list xs
  let mem x (ctx : t) : bool = Name.Set.mem x ctx
  let add x (ctx : t) : t = Name.Set.add x ctx
  let union (ctx1 : t) (ctx2 : t) : t = Name.Set.union ctx1 ctx2
  let dump (ctx : t) = Name.Set.elements ctx
end

module Ctx = struct
  type t = (Name.t * int) Name.Map.t

  let empty : t = Name.Map.empty
  let singleton x fn argc : t = Name.Map.singleton x (fn, argc)
  let add x fn argc (ctx : t) : t = Name.Map.add x (fn, argc) ctx
  let find_opt x (ctx : t) = Name.Map.find_opt x ctx
end
