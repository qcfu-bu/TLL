module Debug : sig
  val enable : unit -> unit
  val disable : unit -> unit
  val exec : (unit -> unit) -> unit
  val fmt : Format.formatter
end = struct
  let state = ref false
  let enable () = state := true
  let disable () = state := false
  let exec f = if !state then f () else ()
  let fmt = Format.formatter_of_out_channel (open_out "log.tll")
end

include Debug

let hole () = failwith "unimplemented"
