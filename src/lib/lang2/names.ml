open Fmt

module Name : sig
  module Make () : sig
    type t

    module Set : Set.S with type elt = t
    module Map : Map.S with type key = t

    val mk : string -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
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
      let pp fmt (s, id) = pf fmt "%s_%d" s id
    end

    include Inner
    module Set = Set.Make (Inner)
    module Map = Map.Make (Inner)
  end
end

module SMeta = Name.Make () (* sort *)
module IMeta = Name.Make () (* implicit *)
module TMeta = Name.Make () (* trait *)
module PMeta = Name.Make () (* pattern  *)
module Const = Name.Make () (* constant *)
module Ind = Name.Make () (* inductive *)
module Constr = Name.Make () (* constructor *)
module Proj = Name.Make () (* projection *)
