open Names

type value =
  | NULL
  | Reg of string
  | Env of int
  | Proj of value * int

and values = value list

and toplevel_entry =
  { name : string
  ; arg : string option
  ; body : instrs
  ; return : value
  }

and toplevel = toplevel_entry list

and ch =
  | Ch of string * value * int * values
  | Stdin
  | Stdout
  | Stderr

and instr =
  | Mov of string * value
  | MakeClo of string * string * int * values
  | CallClo of string * value * value
  | MakeStruct of string * int * values
  | Switch of value * cls
  | Break
  | Open of string * ch
  | Send of string * value
  | Recv of string * value
  | Close of string * value
  | FreeClo of value
  | FreeStruct of value
  | FreeThread

and instrs = instr list
and cl = int * instrs
and cls = cl list
