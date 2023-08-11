module Debug : sig
  val enable : unit -> unit
  val disable : unit -> unit
  val exec : (unit -> unit) -> unit
end = struct
  let state = ref false
  let enable () = state := true
  let disable () = state := false

  let exec f =
    if !state then
      f ()
    else
      ()
end
