open Names

type value =
  | NULL
  | Reg of string
  | Env of int
  | Idx of value * int
[@@deriving show { with_path = false }]

and values = value list

and proc =
  { fname : string
  ; arg : string option
  ; body : instrs
  ; return : value
  }
[@@deriving show { with_path = false }]

and procs = proc list

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
  | Clo of
      { lhs : string
      ; fname : string
      ; env_size : int
      ; env_ext : values
      }
  | Call of
      { lhs : string
      ; fptr : value
      ; aptr : value
      }
  | Struct of
      { lhs : string
      ; ctag : int
      ; size : int
      ; data : values
      }
  | Switch of
      { cond : value
      ; cases : cls
      }
  | Break
  | Open of
      { lhs : string
      ; obj : ch
      }
  | Send of
      { lhs : string
      ; ch : value
      ; mode : int
      }
  | Recv of
      { lhs : string
      ; ch : value
      ; mode : int
      }
  | Close of
      { lhs : string
      ; ch : value
      ; mode : int
      }
  | FreeClo of value
  | FreeStruct of value
  | FreeThread
[@@deriving show { with_path = false }]

and instrs = instr list
and cl = int * instrs
and cls = cl list
