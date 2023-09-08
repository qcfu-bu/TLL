open Fmt

module Name : sig
  module Make () : sig
    type t

    module Set : Set.S with type elt = t
    module Map : Map.S with type key = t

    val mk : string -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val extend : t -> string -> t
    val is_main : t -> bool
    val pp : Format.formatter -> t -> unit
  end
end = struct
  module Make () = struct
    module Inner = struct
      type t = string * int

      let stamp = ref 0

      let mk s =
        incr stamp;
        (s, !stamp)

      let equal x y = snd x = snd y
      let compare x y = Int.compare (snd x) (snd y)
      let extend (s0, _) s1 = mk (s0 ^ s1)
      let is_main (s, _) = s = "main"
      let pp fmt (s, id) = pf fmt "%s_%d" s id
    end

    include Inner
    module Set = Set.Make (Inner)
    module Map = Map.Make (Inner)
  end
end

module SMeta = Name.Make () (* sort *)
module RMeta = Name.Make () (* relevancy *)
module IMeta = Name.Make () (* implicit *)
module PMeta = Name.Make () (* pattern  *)
module Const = Name.Make () (* constant *)
module TName = Name.Make () (* template *)
module Ind = Name.Make () (* inductive *)
module Constr = Name.Make () (* constructor *)
module Record = Name.Make () (* record *)
module Field = Name.Make () (* field *)
