open Fmt
open Names
open Syntax3

let resolve_c c res = Trans12.Resolver.find_cons c [] res

let pp_prelude res fmt () =
  let pp_define fmt c0 =
    let c1 = resolve_c c0 res in
    pf fmt "#define %s_c %d" (C.get_name c1) (C.get_id c1)
  in
  pf fmt "#ifndef prelude_h@.#define prelude_h@.@.@[<v 0>%a@]@.@.#endif"
    (list ~sep:sp pp_define)
    Prelude1.
      [ tt_c
      ; true_c
      ; false_c
      ; o_c
      ; s_c
      ; ascii_c
      ; emptyString_c
      ; string_c
      ; nil_c
      ; cons_c
      ; lnil_c
      ; lcons_c
      ; box_c
      ]

let rec pp_value fmt = function
  | NULL -> pf fmt "0"
  | Reg x -> pf fmt "%s" x
  | Env i -> pf fmt "env[%d]" i
  | Idx (v, i) -> pf fmt "((tll_node)%a)->data[%d]" pp_value v i

let pp_values fmt vs =
  let rec aux fmt vs =
    match vs with
    | [] -> ()
    | [ v ] -> pp_value fmt v
    | v :: vs -> pf fmt "%a,@ %a" pp_value v aux vs
  in
  match vs with
  | [] -> ()
  | _ -> pf fmt ",@;<1 2>@[%a@]" aux vs

let rec gather_var ctx instrs =
  match instrs with
  | [] -> ctx
  | Mov instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Clo instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Call instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Struct instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Switch instr :: instrs ->
    let ctx =
      List.fold_left
        (fun ctx (_, intrs) -> gather_var ctx intrs)
        ctx instr.cases
    in
    gather_var ctx instrs
  | Break :: instrs -> gather_var ctx instrs
  | Open instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Send instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Recv instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | Close instr :: instrs -> gather_var (SSet.add instr.lhs ctx) instrs
  | FreeClo _ :: instrs -> gather_var ctx instrs
  | FreeStruct _ :: instrs -> gather_var ctx instrs
  | FreeThread :: instrs -> gather_var ctx instrs

let pp_xs fmt ctx =
  let xs = SSet.elements ctx in
  let rec aux fmt = function
    | [] -> ()
    | [ x ] -> pf fmt "tll_ptr %s;" x
    | x :: xs -> pf fmt "tll_ptr %s;@;<1 0>%a" x aux xs
  in
  aux fmt xs

let rec pp_proc fmt proc =
  let xs = gather_var SSet.empty proc.body in
  let pp_arg fmt opt =
    match opt with
    | None -> ()
    | Some x -> pf fmt "tll_ptr %s, " x
  in
  pf fmt
    "@[<v 0>tll_ptr %s(%atll_env env)@;\
     <1 0>{@;\
     <1 2>@[<v 0>@[%a@]@;\
     <1 0>%a@;\
     <1 0>return %a@];@;\
     <1 0>}@]" proc.fname pp_arg proc.arg pp_xs xs pp_instrs proc.body pp_value
    proc.return

and pp_procs fmt def =
  match def with
  | [] -> ()
  | [ proc ] -> pp_proc fmt proc
  | proc :: procs -> pf fmt "@[<v 0>%a@]@.@.%a" pp_proc proc pp_procs procs

and pp_instr fmt = function
  | Mov { lhs; rhs } -> pf fmt "instr_mov(&%s, %a);" lhs pp_value rhs
  | Clo { lhs; fname; env_size; env_ext } ->
    pf fmt "@[instr_clo(&%s, &%s, %d, env, %d%a);@]" lhs fname env_size
      (List.length env_ext) pp_values env_ext
  | Call { lhs; fptr; aptr } ->
    pf fmt "instr_call(&%s, %a, %a);" lhs pp_value fptr pp_value aptr
  | Struct { lhs; ctag; size; data = [] } ->
    pf fmt "instr_struct(&%s, %d, %d);" lhs ctag 0
  | Struct { lhs; ctag; size; data } ->
    pf fmt "instr_struct(&%s, %d, %d%a);" lhs ctag 0 pp_values data
  | Switch { cond; cases } ->
    pf fmt "@[<v 0>switch(((tll_node)%a)->tag){@;<1 2>@[%a@]}@]" pp_value cond
      pp_cases cases
  | Break -> pf fmt "break;"
  | Open { lhs; obj } -> (
    match obj with
    | Ch { fname; env_size; env_ext } ->
      pf fmt "instr_open(&%s, &%s, %d, env, %d%a);" lhs fname env_size
        (List.length env_ext) pp_values env_ext
    | Stdout -> pf fmt "instr_prim(&%s, &proc_stdout);" lhs
    | Stdin -> pf fmt "instr_prim(&%s, &proc_stdin);" lhs
    | Stderr -> pf fmt "instr_prim(&%s, &proc_stderr);" lhs)
  | Send { lhs; ch; mode } ->
    pf fmt "instr_send(&%s, %a, %d);" lhs pp_value ch mode
  | Recv { lhs; ch; mode } ->
    pf fmt "instr_recv(&%s, %a, %d);" lhs pp_value ch mode
  | Close { lhs; ch; mode } ->
    pf fmt "instr_close(&%s, %a, %d);" lhs pp_value ch mode
  | FreeClo v -> pf fmt "instr_free_clo(%a);" pp_value v
  | FreeStruct v -> pf fmt "instr_free_struct(%a);" pp_value v
  | FreeThread -> pf fmt "instr_free_thread(env);"

and pp_instrs fmt instrs =
  let rec aux fmt instrs =
    match instrs with
    | [] -> ()
    | [ instr ] -> pp_instr fmt instr
    | instr :: instrs -> pf fmt "%a@;<1 0>%a" pp_instr instr pp_instrs instrs
  in
  pf fmt "@[<v 0>%a@]" aux instrs

and pp_case fmt (i, instr) = pf fmt "@[case %d:@;<1 2>%a@]" i pp_instrs instr

and pp_cases fmt cases =
  match cases with
  | [] -> ()
  | [ case ] -> pp_case fmt case
  | case :: cases -> pf fmt "%a@;<1 0>%a" pp_case case pp_cases cases

let pp_prog fmt (procs, instr, v) =
  let xs = gather_var SSet.empty instr in
  pf fmt
    "#include \"runtime.h\"@.@.%a@.@.@[<v 0>int main()@;\
     <1 0>{@;\
     <1 2>@[<v 0>@[%a@]@;\
     <1 0>tll_env env = 0;@;\
     <1 0>instr_init();@;\
     <1 0>%a@;\
     <1 0>return %a;@]@;\
     <1 0>}@]" pp_procs procs pp_xs xs pp_instrs instr pp_value v
