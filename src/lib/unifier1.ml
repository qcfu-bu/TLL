open Syntax1
open Constraint1

module IResolver : sig
  type t
end = struct
  type t = unit
end

let resolve_tm (eqns : IPrbm.eqns) (m : tm) : tm = m
let resolve_pprbm (eqns : 'a) : unit = ()
