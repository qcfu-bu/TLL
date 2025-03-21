open Fmt
open Names
open Syntax5
open Prelude1

module NSet = Name.Set

let rec gather_lhs0 ctx cmds =
  match cmds with
  | [] -> ctx
  | Move0 (lhs, _) :: cmds -> gather_lhs0 (NSet.add lhs ctx) cmds
  | MkClo0 { lhs } :: cmds -> gather_lhs0 (NSet.add lhs ctx) cmds
  | _ :: cmds -> gather_lhs0 ctx cmds

let rec gather_lhs1 ctx = function
  (* core *)
  | [] -> ctx
  | Move0 _ :: cmds -> gather_lhs1 ctx cmds
  | Move1 (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Env (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | MkClo0 _ :: cmds -> gather_lhs1 ctx cmds
  | MkClo1 { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | SetClo (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | AppF { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | AppC { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Free _ :: cmds -> gather_lhs1 ctx cmds
  (* inductive *)
  | MkBox { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | ReBox { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | SetBox (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | GetBox (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Switch { cases } :: cmds ->
    let ctx = List.fold_left (fun ctx cl ->
        match cl with
        | Case (_, rhs) -> gather_lhs1 ctx rhs
        | Default rhs -> gather_lhs1 ctx rhs)
        ctx cases
    in
    gather_lhs1 ctx cmds
  | Break :: cmds -> gather_lhs1 ctx cmds
  | Absurd :: cmds -> gather_lhs1 ctx cmds
  (* lazy *)
  | Lazy { lhs } :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | SetLazy (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Force (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  (* primitive operators *)
  | Neg (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Add (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Sub (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Mul (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Div (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Mod (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Lte (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Gte (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Lt (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Gt (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Eq (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Chr (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Ord (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Str (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Push (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Cat (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Size (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Indx (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  (* primitive effects *)
  | Print (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Prerr (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | ReadLn (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Fork (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Send (lhs, _, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Recv0 (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Recv1 (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Close0 (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  | Close1 (lhs, _) :: cmds -> gather_lhs1 (NSet.add lhs ctx) cmds
  (* magic *)
  | Magic :: cmds -> gather_lhs1 ctx cmds

let rec pp_expr fmt = function
  | Var n -> Name.pp fmt n
  | Ctag c -> pf fmt "%d" (Constr.id_of c)
  | CtagOf e -> pf fmt "ctagof(%a)" pp_expr e
  | Int i -> int fmt i
  | Char c -> pf fmt "\'%s\'" (Char.escaped c)
  | NULL -> pf fmt "nothing"

let pp_exprs fmt ms =
  let rec aux fmt = function
    | [] -> ()
    | [ m ] -> pp_expr fmt m
    | m :: ms -> pf fmt "%a, %a" pp_expr m aux ms
  in
  pf fmt "%a" aux ms

let rec pp_cmd fmt = function
  (* core *)
  | Move0 (lhs, m) -> pf fmt "%a = %a;" Name.pp lhs pp_expr m
  | Move1 (lhs, m) -> pf fmt "%a = %a;" Name.pp lhs pp_expr m
  | Env (lhs, i) -> pf fmt "%a = env[%d];" Name.pp lhs i
  | MkClo0 { lhs; fn; fvc; argc; } ->
    pf fmt "%a = mkclo(%a, %d, %d);" Name.pp lhs Name.pp fn fvc argc
  | MkClo1 { lhs; fn; fvc; argc; } ->
    pf fmt "%a = mkclo(%a, %d, %d);" Name.pp lhs Name.pp fn fvc argc
  | SetClo (lhs, e, i) -> pf fmt "setclo(%a, %a, %d);" Name.pp lhs pp_expr e i
  | AppF { lhs; fn; args } -> pf fmt "%a = %a(%a);" Name.pp lhs Name.pp fn pp_exprs args
  | AppC { lhs; fn; arg } -> pf fmt "%a = appc(%a, %a);" Name.pp lhs Name.pp fn pp_expr arg
  | Free m -> pf fmt "@[ffree(%a);@]" pp_expr m
  (* inductive *)
  | MkBox { lhs; ctag; argc } ->
    pf fmt "%a = mkbox(%d, %d); //%a" Name.pp lhs (Constr.id_of ctag) argc Constr.pp ctag
  | ReBox { lhs; fip; ctag } ->
    pf fmt "%a = rebox(%a, %d); //%a" Name.pp lhs pp_expr fip (Constr.id_of ctag) Constr.pp ctag
  | SetBox (lhs, e, i) -> pf fmt "setbox(%a, %a, %d);" Name.pp lhs pp_expr e i
  | GetBox (lhs, e, i) -> pf fmt "%a = getbox(%a, %d);" Name.pp lhs pp_expr e i
  | Switch { cond; cases } ->
    pf fmt "@[<v 0>switch(%a){@;<1 2>@[%a@]@;<1 0>}@]" pp_expr cond pp_cases cases
  | Break -> pf fmt "break;"
  | Absurd -> pf fmt "absurd();"
  (* lazy *)
  | Lazy { lhs; fn; fvc } -> pf fmt "%a = lazy(%a, %d);" Name.pp lhs Name.pp fn fvc
  | SetLazy (lhs, e, i) -> pf fmt "setlazy(%a, %a, %d);" Name.pp lhs pp_expr e i 
  | Force (lhs, m) -> pf fmt "@[%a = force(%a);@]" Name.pp lhs pp_expr m
  (* primitive operators *)
  | Neg (lhs, m) -> pf fmt "@[%a = __neg__(%a);@]" Name.pp lhs pp_expr m
  | Add (lhs, m, n) -> pf fmt "@[%a = __add__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Sub (lhs, m, n) -> pf fmt "@[%a = __sub__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mul (lhs, m, n) -> pf fmt "@[%a = __mul__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Div (lhs, m, n) -> pf fmt "@[%a = __div__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mod (lhs, m, n) -> pf fmt "@[%a = __mod__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lte (lhs, m, n) -> pf fmt "@[%a = __lte__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gte (lhs, m, n) -> pf fmt "@[%a = __gte__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lt (lhs, m, n) -> pf fmt "@[%a = __lt__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gt (lhs, m, n) -> pf fmt "@[%a = __gt__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Eq (lhs, m, n) -> pf fmt "@[%a = __eq__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Chr (lhs, m) -> pf fmt "@[%a = __chr__(%a);@]" Name.pp lhs pp_expr m
  | Ord (lhs, m) -> pf fmt "@[%a = __ord__(%a);@]" Name.pp lhs pp_expr m
  | Str (lhs, s) -> pf fmt "@[%a = __str__(\"%s\");@]" Name.pp lhs (String.escaped s)
  | Push (lhs, m, n) -> pf fmt "@[%a = __push__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Cat (lhs, m, n) -> pf fmt "@[%a = __cat__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Size (lhs, m) -> pf fmt "@[%a = __size__(%a);@]" Name.pp lhs pp_expr m
  | Indx (lhs, m, n) -> pf fmt "@[%a = __indx__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  (* primitive effects *)
  | Print (lhs, m) -> pf fmt "@[%a = __print__(%a);@]" Name.pp lhs pp_expr m
  | Prerr (lhs, m) -> pf fmt "@[%a = __prerr__(%a);@]" Name.pp lhs pp_expr m
  | ReadLn (lhs, m) -> pf fmt "@[%a = __readln__(%a);@]" Name.pp lhs pp_expr m
  | Fork (lhs, m) -> pf fmt "@[%a = __fork__(%a);@]" Name.pp lhs pp_expr m
  | Send (lhs, m, n) -> pf fmt "@[%a = __send__(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Recv0 (lhs, m) -> pf fmt "@[%a = __recv0__(%a);@]" Name.pp lhs  pp_expr m
  | Recv1 (lhs, m) -> pf fmt "@[%a = __recv1__(%a);@]" Name.pp lhs  pp_expr m
  | Close0 (lhs, m) -> pf fmt "@[%a = __close0__(%a);@]" Name.pp lhs pp_expr m
  | Close1 (lhs, m) -> pf fmt "@[%a = __close1__(%a);@]" Name.pp lhs pp_expr m
  (* magic *)
  | Magic -> pf fmt "magic();"

and pp_cmds fmt cmds =
  let rec aux fmt = function
    | [] -> ()
    | [ cmd ] -> pp_cmd fmt cmd
    | cmd :: cmds -> pf fmt "%a@;<1 0>%a" pp_cmd cmd aux cmds
  in
  pf fmt "@[<v 0>%a@]" aux cmds

and pp_case fmt = function
  | Case (ctag, rhs) ->
    pf fmt "@[<v 0>case %d: //%a@;<1 2>%a@]" (Constr.id_of ctag) Constr.pp ctag pp_cmds rhs
  | Default rhs -> 
    pf fmt "@[<v 0>default:@;<1 2>%a@]" pp_cmds rhs

and pp_cases fmt cases =
  let rec aux fmt = function
    | [] -> ()
    | [ case ] -> pf fmt "%a" pp_case case
    | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case aux cases
  in
  pf fmt "@[<v 0>%a@]" aux cases

let pp_xs fmt ctx =
  let xs = NSet.elements ctx in
  let rec aux fmt = function
    | [] -> ()
    | [ x ] -> pf fmt "intptr_t %a;" Name.pp x
    | x :: xs -> pf fmt "intptr_t %a;@;<1 0>%a" Name.pp x aux xs
  in
  aux fmt xs

let rec pp_args fmt = function
  | [] -> ()
  | [ x ] -> pf fmt "intptr_t %a" Name.pp x
  | x :: xs -> pf fmt "intptr_t %a, %a" Name.pp x pp_args xs

let pp_dcl fmt dcl =
  match dcl with
  | DefFun0 { fn; args; cmds; ret } ->
    let xs = gather_lhs1 NSet.empty cmds in
    pf fmt "@[<v 0>intptr_t %a(%a) {@;<1 2>@[<v 0>@[%a@]@;<1 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
      Name.pp fn pp_args args pp_xs xs pp_cmds cmds pp_expr ret
  | DefFun1 { fn; cmds; ret } ->
    let xs = gather_lhs1 NSet.empty cmds in
    pf fmt "@[<v 0>intptr_t %a(intptr_t* env) {@;<1 2>@[<v 0>@[%a@]@;<1 0>%a@;<1 0>return %a;@]@;<1 0>}@]"
      Name.pp fn pp_xs xs pp_cmds cmds pp_expr ret

let pp_dcls fmt dcls =
  let rec aux fmt = function
    | [] -> ()
    | [ dcl ] -> pp_dcl fmt dcl
    | dcl :: dcls -> pf fmt "%a@.@.%a" pp_dcl dcl aux dcls
  in
  pf fmt "%a" aux dcls

let rec pp_defs fmt = function
  | [] -> ()
  | DefFun0 { fn; args } :: rest ->
    pf fmt "intptr_t %a(%a);@;<1 0>%a" Name.pp fn pp_args args pp_defs rest
  | DefFun1 { fn; } :: rest ->
    pf fmt "intptr_t %a(intptr_t* env);@;<1 0>%a" Name.pp fn pp_defs rest

let pp_prelude fmt () =
  let open Trans12 in
  let ex1U = State.find_constr ex1_constr [U;L] in
  let ex1L = State.find_constr ex1_constr [L;L] in
  let ttU = State.find_constr tt_constr [U] in
  let trueU = State.find_constr true_constr [] in
  let falseU = State.find_constr false_constr [] in
  pf fmt
    "#ifndef PRELUDE_H@.#define PRELUDE_H@.@.\
     #define __exU__ %d@.\
     #define __exL__ %d@.\
     #define __tt__ %d@.\
     #define __true__ %d@.\
     #define __false__ %d@.@.\
     #endif"
    (Constr.id_of ex1U)
    (Constr.id_of ex1L)
    (Constr.id_of ttU)
    (Constr.id_of trueU)
    (Constr.id_of falseU)

let pp_header fmt prog =
  pf fmt
    "#ifndef MAIN_H@.#define MAIN_H@.@.\
     #include \"runtime.h\"@.@.\
     @[<v 0>%a@]@.\
     #endif"
    pp_defs prog.dcls

let pp_prog fmt prog =
  let xs0 = gather_lhs0 NSet.empty prog.cmds in
  let xs1 = gather_lhs1 NSet.empty prog.cmds in
  pf fmt
    "#include \"main.h\"@.@.\
     @[%a@]@.@.\
     %a@.@.\
     @[<v 0>int main() {@;<1 2>\
     @[<v 0>begin_run();@;<1 0>\
     @[%a@]@;<1 0>\
     %a@;<1 0>\
     end_run();@]@;<1 0>}@]"
    pp_xs xs0
    pp_dcls prog.dcls
    pp_xs xs1
    pp_cmds prog.cmds

let emit prog main_h main_c =
  let prelude_h = Format.formatter_of_out_channel (open_out "gen/prelude.h") in
  pf prelude_h "%s" (str "%a@.@." pp_prelude ());
  pf main_h "%s" (str "%a@.@." pp_header prog);
  pf main_c "%s" (str "%a@.@." pp_prog prog);
  pf Debug.fmt "compilation success";
  pf Debug.fmt "@.@.-----------------------------------------@.@.";

