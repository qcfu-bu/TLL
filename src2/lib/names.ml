open Fmt

(* meta variables *)
module M : sig
  type t

  val mk : unit -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = int

  let stamp = ref 0

  let mk () =
    incr stamp;
    !stamp

  let equal x y = x = y
  let compare x y = Int.compare x y
  let pp fmt id = pf fmt "??%d" id
end

(* data identifiers *)
module D : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = Int.compare (snd x) (snd y)
  let pp fmt (s, id) = pf fmt "%s_d%d" s id
end

(* constructor identifiers *)
module C : sig
  type t

  val mk : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val get_id : t -> int
  val pp : Format.formatter -> t -> unit
end = struct
  type t = string * int

  let stamp = ref 0

  let mk s =
    incr stamp;
    (s, !stamp)

  let equal x y = snd x = snd y
  let compare x y = Int.compare (snd x) (snd y)
  let get_id (_, id) = id
  let pp fmt (s, id) = pf fmt "%s_c%d" s id
end

(* sets *)
module SSet = Set.Make (String)
module MSet = Set.Make (M)
module CSet = Set.Make (C)
module DSet = Set.Make (D)

(* maps *)
module SMap = Map.Make (String)
module MMap = Map.Make (M)
module CMap = Map.Make (C)
module DMap = Map.Make (D)
