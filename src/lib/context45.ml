open Fmt
open Names
open Syntax4

module Vtbl = struct
  type t = expr Name.Map.t

  let find x (vtbl : t) =
    try Name.Map.find x vtbl
    with _ -> failwith "Vtbl.find_name(%a)" Name.pp x

  let add x m (vtbl : t) : t = Name.Map.add x m vtbl
end

module Ctx = struct
  type t = Name.Set.t

  let empty : t = Name.Set.empty
  let singleton x : t = Name.Set.singleton x
  let mem x (ctx : t) : bool = Name.Set.mem x ctx
  let add x (ctx : t) : t = Name.Set.add x ctx
  let union (ctx1 : t) (ctx2 : t) : t = Name.Set.union ctx1 ctx2
  let dump (ctx : t) = Name.Set.elements ctx
end
