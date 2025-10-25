open Fmt
open Names
open Syntax5
open Prelude1
module NMap = Name.Map

type store =
  | Obj
  | Tag

let pp_store fmt = function
  | Obj -> pf fmt "tll_object*"
  | Tag -> pf fmt "unsigned int"

let rec gather_lhs0 ctx cmds =
  match cmds with
  | [] -> ctx
  | Move0 (lhs, _) :: cmds -> gather_lhs0 (NMap.add lhs Obj ctx) cmds
  | MkClo0 { lhs } :: cmds -> gather_lhs0 (NMap.add lhs Obj ctx) cmds
  | _ :: cmds -> gather_lhs0 ctx cmds

let rec gather_lhs1 ctx = function
  (* core *)
  | [] -> ctx
  | Move0 _ :: cmds -> gather_lhs1 ctx cmds
  | Move1 (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Env (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | MkClo0 _ :: cmds -> gather_lhs1 ctx cmds
  | MkClo1 { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | SetClo (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | AppF { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | AppC { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Free _ :: cmds -> gather_lhs1 ctx cmds
  (* inductive *)
  | MkBox { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | ReBox { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | SetBox (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | GetBox (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | GetTag (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Tag ctx) cmds
  | Switch { cases } :: cmds ->
    let ctx =
      List.fold_left
        (fun ctx cl ->
          match cl with
          | Case (_, rhs) -> gather_lhs1 ctx rhs
          | Default rhs -> gather_lhs1 ctx rhs)
        ctx cases
    in
    gather_lhs1 ctx cmds
  | Break :: cmds -> gather_lhs1 ctx cmds
  | Absurd :: cmds -> gather_lhs1 ctx cmds
  (* lazy *)
  | Thunk { lhs } :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | SetThunk (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Force (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  (* primitive operators *)
  | Neg (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Add (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Sub (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Mul (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Div (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Mod (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Lte (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Gte (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Lt (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Gt (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Eq (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Chr (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Ord (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Str (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Push (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Cat (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Size (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Indx (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  (* primitive effects *)
  | Print (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Prerr (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | ReadLn (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Fork (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Send (lhs, _, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Recv0 (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Recv1 (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Close0 (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  | Close1 (lhs, _) :: cmds -> gather_lhs1 (NMap.add lhs Obj ctx) cmds
  (* magic *)
  | Magic :: cmds -> gather_lhs1 ctx cmds

let rec pp_expr fmt = function
  | Box m -> pf fmt "tll_box(%a)" pp_expr m
  | Unbox m -> pf fmt "tll_unbox(%a)" pp_expr m
  | Var n -> Name.pp fmt n
  | Ctag c -> pf fmt "%d" (Constr.id_of c)
  | Int i -> pf fmt "%d" i
  | Char c -> pf fmt "\'%s\'" (Char.escaped c)
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
  | Move0 (lhs, m) -> pf fmt "%a = %a;" Name.pp lhs pp_expr m
  | Move1 (lhs, m) -> pf fmt "%a = %a;" Name.pp lhs pp_expr m
  | Env (lhs, i) -> pf fmt "%a = env[%d];" Name.pp lhs i
  | MkClo0 { lhs; fn; fvc; argc } ->
    pf fmt "%a = tll_closure_make(%a, %d, %d);" Name.pp lhs Name.pp fn fvc argc
  | MkClo1 { lhs; fn; fvc; argc } ->
    pf fmt "%a = tll_closure_make(%a, %d, %d);" Name.pp lhs Name.pp fn fvc argc
  | SetClo (lhs, e, i) ->
    pf fmt "tll_closure_set(%a, %a, %d);" Name.pp lhs pp_expr e i
  | AppF { lhs; fn; args } ->
    pf fmt "%a = %a(%a);" Name.pp lhs Name.pp fn pp_exprs args
  | AppC { lhs; fn; arg } ->
    pf fmt "%a = tll_closure_app(%a, %a);" Name.pp lhs Name.pp fn pp_expr arg
  | Free m -> pf fmt "@[tll_free(%a);@]" pp_expr m
  (* inductive *)
  | MkBox { lhs; ctag; argc } ->
    pf fmt "%a = tll_ctor_make(%d, %d); //%a" Name.pp lhs (Constr.id_of ctag)
      argc Constr.pp ctag
  | ReBox { lhs; fip; ctag } ->
    pf fmt "%a = tll_ctor_set_tag(%a, %d); //%a" Name.pp lhs pp_expr fip
      (Constr.id_of ctag) Constr.pp ctag
  | SetBox (lhs, e, i) ->
    pf fmt "tll_ctor_set(%a, %a, %d);" Name.pp lhs pp_expr e i
  | GetBox (lhs, e, i) ->
    pf fmt "%a = tll_ctor_get(%a, %d);" Name.pp lhs pp_expr e i
  | GetTag (lhs, e) -> pf fmt "%a = tll_ctor_get_tag(%a);" Name.pp lhs pp_expr e
  | Switch { cond; cases } ->
    pf fmt "@[<v 0>switch(%a){@;<1 2>@[%a@]@;<1 0>}@]" pp_expr cond pp_cases
      cases
  | Break -> pf fmt "break;"
  | Absurd -> pf fmt "absurd();"
  (* lazy *)
  | Thunk { lhs; fn; fvc } ->
    pf fmt "%a = tll_thunk_make(%a, %d);" Name.pp lhs Name.pp fn fvc
  | SetThunk (lhs, e, i) ->
    pf fmt "tll_thunk_set(%a, %a, %d);" Name.pp lhs pp_expr e i
  | Force (lhs, m) ->
    pf fmt "@[%a = tll_thunk_force(%a);@]" Name.pp lhs pp_expr m
  (* primitive operators *)
  | Neg (lhs, m) -> pf fmt "@[%a = tll_int_neg(%a);@]" Name.pp lhs pp_expr m
  | Add (lhs, m, n) ->
    pf fmt "@[%a = tll_int_add(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Sub (lhs, m, n) ->
    pf fmt "@[%a = tll_int_sub(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mul (lhs, m, n) ->
    pf fmt "@[%a = tll_int_mul(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Div (lhs, m, n) ->
    pf fmt "@[%a = tll_int_div(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Mod (lhs, m, n) ->
    pf fmt "@[%a = tll_int_mod(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lte (lhs, m, n) ->
    pf fmt "@[%a = tll_int_lte(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gte (lhs, m, n) ->
    pf fmt "@[%a = tll_int_gte(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Lt (lhs, m, n) ->
    pf fmt "@[%a = tll_int_lt(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Gt (lhs, m, n) ->
    pf fmt "@[%a = tll_int_gt(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Eq (lhs, m, n) ->
    pf fmt "@[%a = tll_int_eq(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Chr (lhs, m) -> pf fmt "@[%a = tll_int_to_char(%a);@]" Name.pp lhs pp_expr m
  | Ord (lhs, m) -> pf fmt "@[%a = tll_char_to_int(%a);@]" Name.pp lhs pp_expr m
  | Str (lhs, s) ->
    pf fmt "@[%a = tll_string_make(\"%s\");@]" Name.pp lhs (String.escaped s)
  | Push (lhs, m, n) ->
    pf fmt "@[%a = tll_string_pushback(%a, %a);@]" Name.pp lhs pp_expr m pp_expr
      n
  | Cat (lhs, m, n) ->
    pf fmt "@[%a = tll_string_concat(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Size (lhs, m) ->
    pf fmt "@[%a = tll_string_size(%a);@]" Name.pp lhs pp_expr m
  | Indx (lhs, m, n) ->
    pf fmt "@[%a = tll_string_at(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  (* primitive effects *)
  | Print (lhs, m) ->
    pf fmt "@[%a = tll_effect_print(%a);@]" Name.pp lhs pp_expr m
  | Prerr (lhs, m) ->
    pf fmt "@[%a = tll_effect_prerr(%a);@]" Name.pp lhs pp_expr m
  | ReadLn (lhs, m) ->
    pf fmt "@[%a = tll_effect_readln(%a);@]" Name.pp lhs pp_expr m
  | Fork (lhs, m) ->
    pf fmt "@[%a = tll_effect_fork(%a);@]" Name.pp lhs pp_expr m
  | Send (lhs, m, n) ->
    pf fmt "@[%a = tll_effect_send(%a, %a);@]" Name.pp lhs pp_expr m pp_expr n
  | Recv0 (lhs, m) ->
    pf fmt "@[%a = tll_effect_recv0(%a);@]" Name.pp lhs pp_expr m
  | Recv1 (lhs, m) ->
    pf fmt "@[%a = tll_effect_recv1(%a);@]" Name.pp lhs pp_expr m
  | Close0 (lhs, m) ->
    pf fmt "@[%a = tll_effect_close0(%a);@]" Name.pp lhs pp_expr m
  | Close1 (lhs, m) ->
    pf fmt "@[%a = tll_effect_close1(%a);@]" Name.pp lhs pp_expr m
  (* magic *)
  | Magic -> pf fmt "tll_magic();"

and pp_cmds fmt cmds =
  let rec aux fmt = function
    | [] -> ()
    | [ cmd ] -> pp_cmd fmt cmd
    | cmd :: cmds -> pf fmt "%a@;<1 0>%a" pp_cmd cmd aux cmds
  in
  pf fmt "@[<v 0>%a@]" aux cmds

and pp_case fmt = function
  | Case (ctag, rhs) ->
    pf fmt "@[<v 0>case %d: //%a@;<1 2>%a@]" (Constr.id_of ctag) Constr.pp ctag
      pp_cmds rhs
  | Default rhs -> pf fmt "@[<v 0>default:@;<1 2>%a@]" pp_cmds rhs

and pp_cases fmt cases =
  let rec aux fmt = function
    | [] -> ()
    | [ case ] -> pf fmt "%a" pp_case case
    | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case aux cases
  in
  pf fmt "@[<v 0>%a@]" aux cases

let pp_xs fmt ctx =
  let xs = NMap.to_list ctx in
  let rec aux fmt = function
    | [] -> ()
    | [ (x, ty) ] -> pf fmt "%a %a;" pp_store ty Name.pp x
    | (x, ty) :: xs -> pf fmt "%a %a;@;<1 0>%a" pp_store ty Name.pp x aux xs
  in
  aux fmt xs

let rec pp_args fmt = function
  | [] -> ()
  | [ x ] -> pf fmt "tll_object* %a" Name.pp x
  | x :: xs -> pf fmt "tll_object* %a, %a" Name.pp x pp_args xs

let pp_dcl fmt dcl =
  match dcl with
  | DefFun0 { fn; args; cmds; ret } ->
    let xs = gather_lhs1 NMap.empty cmds in
    pf fmt
      "@[<v 0>tll_object* %a(%a) {@;\
       <1 2>@[<v 0>@[%a@]@;\
       <1 0>%a@;\
       <1 0>return %a;@]@;\
       <1 0>}@]"
      Name.pp fn pp_args args pp_xs xs pp_cmds cmds pp_expr ret
  | DefFun1 { fn; cmds; ret } ->
    let xs = gather_lhs1 NMap.empty cmds in
    pf fmt
      "@[<v 0>tll_object* %a(tll_object* env[]) {@;\
       <1 2>@[<v 0>@[%a@]@;\
       <1 0>%a@;\
       <1 0>return %a;@]@;\
       <1 0>}@]"
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
    pf fmt "tll_object* %a(%a);@;<1 0>%a" Name.pp fn pp_args args pp_defs rest
  | DefFun1 { fn } :: rest ->
    pf fmt "tll_object* %a(tll_object* env[]);@;<1 0>%a" Name.pp fn pp_defs rest

let pp_prelude fmt () =
  let open Trans12 in
  let ex1U = State.find_constr ex1_constr [ U; L ] in
  let ex1L = State.find_constr ex1_constr [ L; L ] in
  let ttU = State.find_constr tt_constr [ U ] in
  let trueU = State.find_constr true_constr [] in
  let falseU = State.find_constr false_constr [] in
  pf fmt
    "#ifndef PRELUDE_H@.#define PRELUDE_H@.@.#define __exU__ %d@.#define \
     __exL__ %d@.#define __tt__ %d@.#define __true__ %d@.#define __false__ \
     %d@.@.#endif"
    (Constr.id_of ex1U) (Constr.id_of ex1L) (Constr.id_of ttU)
    (Constr.id_of trueU) (Constr.id_of falseU)

let pp_header fmt prog =
  pf fmt
    "#ifndef MAIN_H@.#define MAIN_H@.@.#include \"runtime.h\"@.@.@[<v \
     0>%a@]@.#endif"
    pp_defs prog.dcls

let pp_prog fmt prog =
  let xs0 = gather_lhs0 NMap.empty prog.cmds in
  let xs1 = gather_lhs1 NMap.empty prog.cmds in
  pf fmt
    "#include \"main.h\"@.@.@[%a@]@.@.%a@.@.@[<v 0>int main() {@;\
     <1 2>@[<v 0>tll_init();@;\
     <1 0>@[%a@]@;\
     <1 0>%a@;\
     <1 0>tll_exit();@]@;\
     <1 0>}@]"
    pp_xs xs0 pp_dcls prog.dcls pp_xs xs1 pp_cmds prog.cmds

let emit prog main_h main_c =
  let prelude_h = Format.formatter_of_out_channel (open_out "gen/prelude.h") in
  pf prelude_h "%s" (str "%a@.@." pp_prelude ());
  pf main_h "%s" (str "%a@.@." pp_header prog);
  pf main_c "%s" (str "%a@.@." pp_prog prog);
  pf Debug.fmt "compilation success";
  pf Debug.fmt "@.@.-----------------------------------------@.@."
