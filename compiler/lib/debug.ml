module Debug : sig
  val enable : unit -> unit
  val disable : unit -> unit
  val exec : (unit -> unit) -> unit
  val fmt : Format.formatter
  val eqn_count_incr : unit -> unit
  val eqn_count_get : unit -> int
end = struct
  let state = ref false
  let enable () = state := true
  let disable () = state := false
  let eqn_count = ref 0
  let eqn_count_incr () = incr eqn_count
  let eqn_count_get () = !eqn_count

  let exec f =
    if !state then
      f ()
    else
      ()

  let fmt = Format.formatter_of_out_channel (open_out "log.tll")
end

include Debug

let hole () = failwith "unimplemented"
