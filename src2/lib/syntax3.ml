open Names

type value =
  | NULL
  | Reg of string
  | Env of int
  | Idx of value * int
[@@deriving show { with_path = false }]

and values = value list

and toplevel_entry =
  { fname : string
  ; arg : string option
  ; body : instrs
  ; return : value
  }
[@@deriving show { with_path = false }]

and toplevel = toplevel_entry list

and ch =
  | Ch of
      { fname : string
      ; env_size : int
      ; env_ext : values
      }
  | Stdin
  | Stdout
  | Stderr
[@@deriving show { with_path = false }]

and instr =
  | Mov of
      { lhs : string
      ; rhs : value
      }
  | MakeClo of
      { lhs : string
      ; fname : string
      ; env_size : int
      ; env_ext : values
      }
  | CallClo of
      { lhs : string
      ; fptr : value
      ; aptr : value
      }
  | MakeStruct of
      { lhs : string
      ; ctag : int
      ; size : int
      ; data : values
      }
  | Switch of
      { cond : value
      ; case : cls
      }
  | Break
  | Open of
      { lhs : string
      ; obj : ch
      }
  | Send of
      { lhs : string
      ; ch : value
      }
  | Recv of
      { lhs : string
      ; ch : value
      }
  | Close of
      { lhs : string
      ; ch : value
      }
  | FreeClo of value
  | FreeStruct of value
  | FreeThread
[@@deriving show { with_path = false }]

and instrs = instr list
and cl = int * instrs
and cls = cl list
