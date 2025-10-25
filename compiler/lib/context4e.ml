open Fmt
open Syntax4

module Entry : sig
  type t

  val mk : expr -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val dump : t -> expr
end = struct
  type t = expr * int

  let stamp = ref (-0)

  let mk m : t =
    incr stamp;
    (m, !stamp)

  let equal (e1 : t) (e2 : t) = snd e1 = snd e2
  let compare (e1 : t) (e2 : t) = Int.compare (snd e1) (snd e2)
  let dump (e : t) = fst e
end

module Mem = struct
  module IMap = Map.Make (Int)
  module ESet = Set.Make (Entry)

  type t = ESet.t IMap.t list

  let empty : t = []
  let new_scope (mem : t) = IMap.empty :: mem

  let push_stack size e (mem : t) : t =
    match mem with
    | [] -> failwith "push_stack(empty_scope)"
    | scope :: mem -> (
      try
        let set = IMap.find size scope in
        IMap.add size (ESet.add e set) scope :: mem
      with
      | _ -> IMap.add size (ESet.singleton e) scope :: mem)

  let pop_stack size (mem : t) : (expr * t) option =
    let rec aux mem =
      match mem with
      | [] -> None
      | scope :: mem -> (
        try
          let set = IMap.find size scope in
          match ESet.max_elt_opt set with
          | Some e ->
            let scope = IMap.add size (ESet.remove e set) scope in
            Some (Entry.dump e, scope :: mem)
          | _ ->
            let opt = aux mem in
            Option.map (fun (m, mem) -> (m, scope :: mem)) opt
        with
        | _ ->
          let opt = aux mem in
          Option.map (fun (m, mem) -> (m, scope :: mem)) opt)
    in
    aux mem

  let dump_scope (mem : t) : exprs * t =
    match mem with
    | [] -> failwith "dump_scope(empty)"
    | scope :: mem ->
      let scope = IMap.bindings scope in
      let scope =
        List.concat_map
          (fun (_, stack) -> stack |> ESet.elements |> List.map Entry.dump)
          scope
      in
      (scope, mem)

  let rec merge (mem1 : t) (mem2 : t) : t =
    match (mem1, mem2) with
    | [], [] -> []
    | scope1 :: mem1, scope2 :: mem2 ->
      let scope =
        IMap.merge
          (fun size opt1 opt2 ->
            match (opt1, opt2) with
            | None, _ -> opt2
            | _, None -> opt1
            | Some set1, Some set2 -> Some ESet.(union set1 set2))
          scope1 scope2
      in
      scope :: merge mem1 mem2
    | _ ->
      let sz1 = List.length mem1 in
      let sz2 = List.length mem2 in
      failwith "merge(scope_uneven, %d, %d)" sz1 sz2

  let rec diff (mem1 : t) (mem2 : t) : t =
    match (mem1, mem2) with
    | [], [] -> []
    | scope1 :: mem1, scope2 :: mem2 ->
      let scope =
        IMap.merge
          (fun size opt1 opt2 ->
            match (opt1, opt2) with
            | None, _ -> None
            | _, None -> opt1
            | Some set1, Some set2 -> Some ESet.(diff set1 set2))
          scope1 scope2
      in
      scope :: merge mem1 mem2
    | _ ->
      let sz1 = List.length mem1 in
      let sz2 = List.length mem2 in
      failwith "diff(scope_uneven, %d, %d)" sz1 sz2

  let union (mems : t list) : t =
    match mems with
    | [] -> []
    | initial :: mems -> List.fold_left merge initial mems
end
