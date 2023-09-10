open Fmt
open Names
open Syntax4

let pp_sort fmt = function
  | U -> pf fmt "U"
  | L -> pf fmt "L"

let pp_expr fmt = function
  | Var n -> Name.pp fmt n
  | Ctag c -> Constr.pp fmt c
  | Int i -> int fmt i
  | Char c -> char fmt c
  | String s -> string fmt s
  | NULL -> pf fmt "NULL"

let pp_exprs fmt ms =
  let rec aux fmt = function
    | [] -> ()
    | [ m ] -> pp_expr fmt m
    | m :: ms -> pf fmt "%a, %a" pp_expr m aux ms
  in
  pf fmt "%a" aux ms

let pp_args fmt args =
  let rec aux fmt = function
    | [] -> ()
    | [ (s, n) ] -> pf fmt "%a%%%a" Name.pp n pp_sort s
    | (s, n) :: args -> pf fmt "%a%%%a, %a" Name.pp n pp_sort s aux args
  in
  pf fmt "%a" aux args

let rec pp_cmd fmt = function
  (* core *)
  | Move (lhs, m) -> pf fmt "val %a := %a;" Name.pp lhs pp_expr m
  | Fun { lhs; fn; args; cmds; ret } ->
    pf fmt "@[val %a :=@;<1 2>@[fn %a(%a) {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@];@]"
      Name.pp lhs Name.pp fn pp_args args pp_cmds cmds pp_expr ret
  | App { lhs; fn; args } ->
    let args = List.map snd args in
    pf fmt "@[val %a := %a(%a);@]" Name.pp lhs pp_expr fn pp_exprs args
  | Free m -> pf fmt "@[free(%a);@]" pp_expr m
  (* inductive *)
  | MkConstr { lhs; cons; ctag; args } ->
    (match cons with
     | Some m -> 
       pf fmt "@[val %a := reconstr(%a, %a, %a);@]"
         Name.pp lhs pp_expr m Constr.pp ctag pp_exprs args
     | None ->
       pf fmt "@[val %a := mkconstr(%a, [%a]);@]"
         Name.pp lhs Constr.pp ctag pp_exprs args)
  | Match0 { cond; cases } ->
    pf fmt "@[match(%a){@;<1 2>@[%a@]@;<1 0>}@]" pp_expr cond pp_cases cases
  | Match1 { cond; sort; cases } ->
    pf fmt "@[match[%a](%a){@;<1 2>@[%a@]@;<1 0>}@]" pp_sort sort pp_expr cond pp_cases cases
  | Absurd -> pf fmt "absurd;"
  | Lazy { lhs; cmds; ret } ->
    pf fmt "@[val %a :=@;<1 2>@[lazy {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@];@]"
      Name.pp lhs pp_cmds cmds pp_expr ret
  | Force (lhs, m) -> pf fmt "@[val %a := force(%a);@]" Name.pp lhs pp_expr m
  (* primitive operators *)
  | Neg (lhs, m) -> pf fmt "@[val %a := neg(%a);@]" Name.pp lhs pp_expr m
  | Add (lhs, m, n) -> pf fmt "@[val %a := add(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Sub (lhs, m, n) -> pf fmt "@[val %a := sub(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mul (lhs, m, n) -> pf fmt "@[val %a := mul(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Div (lhs, m, n) -> pf fmt "@[val %a := div(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mod (lhs, m, n) -> pf fmt "@[val %a := mod(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lte (lhs, m, n) -> pf fmt "@[val %a := lte(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gte (lhs, m, n) -> pf fmt "@[val %a := gte(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lt (lhs, m, n) -> pf fmt "@[val %a := lt(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gt (lhs, m, n) -> pf fmt "@[val %a := gt(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Eq (lhs, m, n) -> pf fmt "@[val %a := eq(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Chr (lhs, m) -> pf fmt "@[val %a := chr(%a);@]" Name.pp lhs pp_expr m
  | Ord (lhs, m) -> pf fmt "@[val %a := ord(%a);@]" Name.pp lhs pp_expr m
  | Push (lhs, m, n) -> pf fmt "@[val %a := push(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Cat (lhs, m, n) -> pf fmt "@[val %a := cat(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Size (lhs, m) -> pf fmt "@[val %a := size(%a);@]" Name.pp lhs pp_expr m
  | Indx (lhs, m, n) -> pf fmt "@[val %a := indx(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  (* primitive effects *)
  | Print (lhs, m) -> pf fmt "@[val %a := print(%a);@]" Name.pp lhs pp_expr m
  | Prerr (lhs, m) -> pf fmt "@[val %a := prerr(%a);@]" Name.pp lhs pp_expr m
  | ReadLn (lhs, m) -> pf fmt "@[val %a := readln(%a);@]" Name.pp lhs pp_expr m
  | Fork (lhs, m) -> pf fmt "@[val %a := fork(%a);@]" Name.pp lhs pp_expr m
  | Send (lhs, m, n) -> pf fmt "@[val %a := send(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Recv (lhs, sort, m) -> pf fmt "@[val %a := recv[%a](%a);@]" Name.pp lhs pp_sort sort pp_expr m
  | Close (lhs, role, m) -> pf fmt "@[val %a := close[%b](%a);@]" Name.pp lhs role pp_expr m
  (* magic *)
  | Magic -> pf fmt "magic;"

and pp_cmds fmt cmds =
  let rec aux fmt = function
    | [] -> ()
    | [ cmd ] -> pp_cmd fmt cmd
    | cmd :: cmds -> pf fmt "%a@;<1 0>%a" pp_cmd cmd aux cmds
  in
  pf fmt "@[<v 0>%a@]" aux cmds

and pp_case fmt case =
  let rec pp_args fmt = function
    | [] -> ()
    | [ x ] -> Name.pp fmt x
    | x :: xs -> pf fmt "%a, %a" Name.pp x pp_args xs
  in
  pf fmt "@[<v 0>%a(%a) => {@;<1 2>%a@;<1 0>}@]"
    Constr.pp case.ctag pp_args case.args pp_cmds case.rhs

and pp_cases fmt cases =
  let rec aux fmt = function
    | [] -> ()
    | [ case ] -> pp_case fmt case
    | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case aux cases
  in
  pf fmt "@[<v 0>%a@]" aux cases

let pp_dcl fmt = function
  | Main { cmds; ret } ->
    pf fmt "main := { %a; ret %a; }" pp_cmds cmds pp_expr ret
  | DefFun { fn; args; cmds; ret } ->
    pf fmt "@[<v 0>fn %a(%a) {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
      Name.pp fn pp_args args pp_cmds cmds pp_expr ret
  | DefVal { lhs; cmds; ret } ->
    pf fmt "%a := { %a; ret %a; } " Name.pp lhs pp_cmds cmds pp_expr ret

let pp_dcls fmt dcls =
  let break fmt _ = pf fmt "@.@." in
  pf fmt "%a" (list ~sep:break pp_dcl) dcls
