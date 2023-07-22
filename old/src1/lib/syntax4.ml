type prim =
  | Stdin
  | Stdout
  | Stderr
[@@deriving show { with_path = false }]

type value =
  | Reg of string
  | Env of int
  | Idx of value * int
  | NULL
[@@deriving show { with_path = false }]

and values = value list

and proc =
  | GFun of
      { fname : string
      ; param : string list
      ; body : instrs
      ; return : value
      }
  | LFun of
      { fname : string
      ; param : string option
      ; body : instrs
      ; return : value
      }

and procs = proc list

and instr =
  | Init of
      { lhs : string
      ; rhs : value
      }
  | Mov of
      { lhs : string
      ; rhs : value
      }
  | Clo of
      { lhs : string
      ; fname : string
      ; env : values
      }
  | Call of
      { lhs : string
      ; fname : string
      ; aptrs : values
      }
  | App of
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
      ; mode : prim
      }
  | Fork of
      { lhs : string
      ; fname : string
      ; env : values
      }
  | Recv of
      { lhs : string
      ; ch : value
      }
  | Send of
      { lhs : string
      ; ch : value
      ; msg : value
      }
  | Close of
      { lhs : string
      ; ch : value
      }
  | FreeClo of value
  | FreeStruct of value
  | FreeThread

and instrs = instr list
and cl = int * instrs
and cls = cl list
