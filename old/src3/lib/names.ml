open Fmt

module Base : sig
  module Make () : sig
    type t

    module Set : Set.S with type elt = t
    module Map : Map.S with type key = t

    val mk : string -> t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val extend : t -> string -> t
    val name_of : t -> string
    val id_of : t -> int
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
      let name_of (s, _) = s
      let id_of (_, i) = i
      let pp fmt (s, id) = pf fmt "%s_%d" s id
    end

    include Inner
    module Set = Set.Make (Inner)
    module Map = Map.Make (Inner)
  end
end

module SMeta = Base.Make ()  (* sort *)
module RMeta = Base.Make ()  (* relevancy *)
module IMeta = Base.Make ()  (* implicit *)
module PMeta = Base.Make ()  (* pattern  *)
module Const = Base.Make ()  (* constant *)
module TName = Base.Make ()  (* template *)
module Ind = Base.Make ()    (* inductive *)
module Constr = Base.Make () (* constructor *)
module Record = Base.Make () (* record *)
module Field = Base.Make ()  (* field *)
module Name = Base.Make ()     (* name *)
