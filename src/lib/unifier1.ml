open Syntax1
open Constraint1

module IResolver : sig
  type t
end = struct
  type t = unit
end

let solve_pprbm (eqns : PPrbm.eqns) : 'a = failwith "unimplemented"
let resolve_iprbm (eqns : IPrbm.eqns) (m : tm) : tm = m
let resolve_pprbm (eqns : PPrbm.eqns) (m : tm) : tm = m
