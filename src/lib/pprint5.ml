open Fmt
open Names
open Syntax5

let rec pp_expr fmt = function
  | Var n -> Name.pp fmt n
  | Ctag c -> Constr.pp fmt c
  | CtagOf e -> pf fmt "ctagof(%a)" pp_expr e
  | Int i -> int fmt i
  | Char c -> char fmt c
  | NULL -> pf fmt "NULL"

let pp_exprs fmt ms =
  let rec aux fmt = function
    | [] -> ()
    | [ m ] -> pp_expr fmt m
    | m :: ms -> pf fmt "%a, %a" pp_expr m aux ms
  in
  pf fmt "%a" aux ms

let rec pp_cmd fmt = function
  (* core *)
  | Move0 (lhs, m) -> pf fmt "move0(%a, %a);" Name.pp lhs pp_expr m
  | Move1 (lhs, m) -> pf fmt "move1(%a, %a);" Name.pp lhs pp_expr m
  | Env (lhs, i) -> pf fmt "%a := env[%d];" Name.pp lhs i
  | MkClo0 { lhs; fn; fvc; argc; } ->
    pf fmt "mkclo0(%a, %a, fvc:=%d, argc:=%d);" Name.pp lhs Name.pp fn fvc argc
  | MkClo1 { lhs; fn; fvc; argc; } ->
    pf fmt "mkclo1(%a, %a, fvc:=%d, argc:=%d);" Name.pp lhs Name.pp fn fvc argc
  | SetClo (lhs, e, i) -> pf fmt "setclo(%a, %a, %d);" Name.pp lhs pp_expr e i
  | AppF { lhs; fn; args } -> pf fmt "%a := %a(%a);" Name.pp lhs Name.pp fn pp_exprs args
  | AppC { lhs; fn; arg } -> pf fmt "appc(%a, %a, %a);" Name.pp lhs Name.pp fn pp_expr arg
  | Free m -> pf fmt "@[free(%a);@]" pp_expr m
  (* inductive *)
  | MkBox { lhs; ctag; argc } -> pf fmt "mkbox(%a, %a, %d);" Name.pp lhs Constr.pp ctag argc
  | ReBox { lhs; fip; ctag } -> pf fmt "rebox(%a, %a, %a);" Name.pp lhs pp_expr fip Constr.pp ctag
  | SetBox (lhs, e, i) -> pf fmt "setbox(%a, %a, %d);" Name.pp lhs pp_expr e i
  | GetBox (lhs, e, i) -> pf fmt "getbox(%a, %a, %d);" Name.pp lhs pp_expr e i
  | Switch { cond; cases } ->
    pf fmt "@[switch(%a){@;<1 2>@[%a@]@;<1 0>}@]" pp_expr cond pp_cases cases
  | Break -> pf fmt "break;"
  | Absurd -> pf fmt "absurd;"
  (* lazy *)
  | Lazy { lhs; fn; fvc } -> pf fmt "lazy(%a, %a, %d);" Name.pp lhs Name.pp fn fvc
  | SetLazy (lhs, e, i) -> pf fmt "setlazy(%a, %a, %d);" Name.pp lhs pp_expr e i 
  | Force (lhs, m) -> pf fmt "@[force(%a, %a);@]" Name.pp lhs pp_expr m
  (* primitive operators *)
  | Neg (lhs, m) -> pf fmt "@[neg(%a, %a);@]" Name.pp lhs pp_expr m
  | Add (lhs, m, n) -> pf fmt "@[add(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Sub (lhs, m, n) -> pf fmt "@[sub(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mul (lhs, m, n) -> pf fmt "@[mul(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Div (lhs, m, n) -> pf fmt "@[div(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mod (lhs, m, n) -> pf fmt "@[mod(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lte (lhs, m, n) -> pf fmt "@[lte(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gte (lhs, m, n) -> pf fmt "@[gte(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lt (lhs, m, n) -> pf fmt "@[lt(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gt (lhs, m, n) -> pf fmt "@[gt(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Eq (lhs, m, n) -> pf fmt "@[eq(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Chr (lhs, m) -> pf fmt "@[chr(%a, %a);@]" Name.pp lhs pp_expr m
  | Ord (lhs, m) -> pf fmt "@[ord(%a, %a);@]" Name.pp lhs pp_expr m
  | Str (lhs, s) -> pf fmt "@[str(%a, \"%s\")@]" Name.pp lhs (String.escaped s)
  | Push (lhs, m, n) -> pf fmt "@[push(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Cat (lhs, m, n) -> pf fmt "@[cat(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Size (lhs, m) -> pf fmt "@[size(%a, %a);@]" Name.pp lhs pp_expr m
  | Indx (lhs, m, n) -> pf fmt "@[indx(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  (* primitive effects *)
  | Print (lhs, m) -> pf fmt "@[print(%a, %a);@]" Name.pp lhs pp_expr m
  | Prerr (lhs, m) -> pf fmt "@[prerr(%a, %a);@]" Name.pp lhs pp_expr m
  | ReadLn (lhs, m) -> pf fmt "@[readln(%a, %a);@]" Name.pp lhs pp_expr m
  | Fork (lhs, m) -> pf fmt "@[fork(%a, %a);@]" Name.pp lhs pp_expr m
  | Send (lhs, m, n) -> pf fmt "@[send(%a, %a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Recv0 (lhs, m) -> pf fmt "@[recv0(%a, %a);@]" Name.pp lhs pp_expr m
  | Recv1 (lhs, m) -> pf fmt "@[recv1(%a, %a);@]" Name.pp lhs pp_expr m
  | Close0 (lhs, m) -> pf fmt "@[close0(%a, %a);@]" Name.pp lhs pp_expr m
  | Close1 (lhs, m) -> pf fmt "@[close1(%a, %a);@]" Name.pp lhs pp_expr m
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
  pf fmt "@[<v 0>%a => {@;<1 2>%a@;<1 0>}@]" Constr.pp case.ctag pp_cmds case.rhs

and pp_cases fmt cases =
  let rec aux fmt = function
    | [] -> ()
    | [ case ] -> pp_case fmt case
    | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case aux cases
  in
  pf fmt "@[<v 0>%a@]" aux cases

let pp_dcl fmt dcl =
  let rec pp_args fmt = function
    | [] -> ()
    | [ x ] -> Name.pp fmt x
    | x :: xs -> pf fmt "%a, %a" Name.pp x pp_args xs
  in
  match dcl with
  | DefFun0 { fn; args; cmds; ret } ->
    pf fmt "@[<v 0>fn %a(%a) {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
      Name.pp fn pp_args args pp_cmds cmds pp_expr ret
  | DefFun1 { fn; cmds; ret } ->
    pf fmt "@[<v 0>fn %a(env) {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
      Name.pp fn pp_cmds cmds pp_expr ret

let pp_dcls fmt dcls =
  let rec aux fmt = function
    | [] -> ()
    | [ dcl ] -> pp_dcl fmt dcl
    | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl aux dcls
  in
  pf fmt "%a" aux dcls

let pp_prog fmt prog =
  pf fmt "%a@.@.@[<v 0>main {@;<1 2>@[<v 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
    pp_dcls prog.dcls pp_cmds prog.cmds pp_expr prog.ret
