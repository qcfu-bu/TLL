open Bindlib
open Names
open Syntax1
open Context1e
open Prelude1


let rec whnf ?(expand = true) (env : Env.t) m = 
  let (mod) x y =
    let r = x mod y in
    if r < 0 then r + abs(y) else r
  in
  match m with
  (* inference *)
  | Ann (m, a) -> whnf ~expand env m
  (* core *)
  | Var x when expand ->
    (try whnf ~expand env (Env.find_var x env) with _ -> Var x)
  | Const (x, ss) when expand ->
    (try
       let sch = Env.find_const x env in
       whnf ~expand env (msubst sch (Array.of_list ss))
     with _ -> Const (x, ss))
  | App _ as m ->
    let hd, ms = unApps m in
    let hd = whnf ~expand env hd in
    (match hd with
     | Fun (guard, _, bnd) when expand ->
       let cls = subst bnd hd in
       (match match_cls ~expand env guard cls ms with
        | Some (Some rhs, rst) -> whnf ~expand env (mkApps rhs rst)
        | _ -> mkApps hd ms)
     | Fun (guard, _, bnd) when not (binder_occur bnd) ->
       let cls = subst bnd hd in
       (match match_cls ~expand env guard cls ms with
        | Some (Some rhs, rst) -> whnf ~expand env (mkApps rhs rst)
        | _ -> mkApps hd ms)
     | _ -> mkApps hd ms)
  | Let (_, m, bnd) ->
    let m = whnf ~expand env m in
    whnf ~expand env (subst bnd m)
  (* inductive *)
  | Match (guard, ms, a, cls) ->
    let ms = List.map (whnf ~expand env) ms in
    (match match_cls ~expand env guard cls ms with
     | Some (Some rhs, []) -> whnf ~expand env rhs
     | _ -> Match (guard, ms, a, cls))
  (* monadic *)
  | MLet (m, bnd) ->
    let m = whnf ~expand env m in
    (match m with
     | Return m ->
       let m = whnf ~expand env m in
       whnf ~expand env (subst bnd m)
     | _ -> MLet (m, bnd))
  (* primitive *)
  | Neg m ->
    (match whnf ~expand env m with
     | Int i -> Int (-i)
     | m -> Neg m)
  | Add (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j -> Int (i + j)
     | m, n -> Add (m, n))
  | Sub (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j -> Int (i - j)
     | m, n -> Sub (m, n))
  | Mul (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j -> Int (i * j)
     | m, n -> Mul (m, n))
  | Div (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int 0 -> Int 0
     | Int i, Int j -> Int (i / j)
     | m, n -> Div (m, n))
  | Mod (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int 0 -> Int 0
     | Int i, Int j -> Int (i mod j)
     | m, n -> Mod (m, n))
  | Lte (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j ->
       if i <= j
       then Constr (true_constr, [], [], [])
       else Constr (false_constr, [], [], [])
     | m, n -> Lte (m, n))
  | Gte (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j ->
       if i >= j
       then Constr (true_constr, [], [], [])
       else Constr (false_constr, [], [], [])
     | m, n -> Gte (m, n))
  | Lt (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j ->
       if i < j
       then Constr (true_constr, [], [], [])
       else Constr (false_constr, [], [], [])
     | m, n -> Lt (m, n))
  | Gt (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j ->
       if i > j
       then Constr (true_constr, [], [], [])
       else Constr (false_constr, [], [], [])
     | m, n -> Gt (m, n))
  | Eq (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | Int i, Int j ->
       if i = j
       then Constr (true_constr, [], [], [])
       else Constr (false_constr, [], [], [])
     | m, n -> Eq (m, n))
  | Chr m ->
    (match whnf ~expand env m with
     | Int i -> Char (Char.chr (i mod 256))
     | m -> Chr m)
  | Ord m ->
    (match whnf ~expand env m with
     | Char c -> Int (Char.code c)
     | m -> Ord m)
  | Push (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | String s, Char c -> String (s ^ String.make 1 c)
     | m, n -> Push (m, n))
  | Cat (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | String s1, String s2 -> String (s1 ^ s2)
     | m, n -> Cat (m, n))
  | Size m ->
    (match whnf ~expand env m with
     | String s -> Int (String.length s)
     | m -> Size m)
  | Indx (m, n) ->
    (match whnf ~expand env m, whnf ~expand env n with
     | String "", Int i -> Char '\000'
     | String s, Int i -> Char (String.(get s (i mod (length s))))
     | m, n -> Indx (m, n))
  (* primitive session *)
  | Ch (role, m) -> Ch (role, whnf ~expand env m)
  (* other *)
  | m -> m

and match_cls ?(expand = true) (env : Env.t) guard cls ms =
  let rec check_guard guard ms =
    match (guard, ms) with
    | true :: guard, m :: ms ->
      (match whnf ~expand env m with
       | Constr _ as m ->
         Option.map (fun (ms, ns) -> (m :: ms, ns)) (check_guard guard ms)
       | _ -> None)
    | true :: guard, _ -> None
    | false :: guard, m :: ms ->
      Option.map (fun (ms, ns) -> (m :: ms, ns)) (check_guard guard ms)
    | false :: guard, [] -> None
    | [], ms -> Some ([], ms)
  and psubst (p0s, bnd) ms =
    let rec match_p0 p0 m =
      match p0 with
      | P0Rel -> [ m ]
      | P0Constr (c1, p0s) ->
        (match whnf ~expand env m with
         | Constr (c2, _, _, ms)
           when Constr.equal c1 c2 -> match_p0s p0s ms
         | _ -> failwith "equality1e.match_p0")
      | _ -> failwith "equality1e.match_p0"
    and match_p0s p0s ms =
      List.fold_left2 (fun acc p0 m -> acc @ match_p0 p0 m) [] p0s ms
    in
    let ms = match_p0s p0s ms in
    msubst bnd (Array.of_list ms)
  in
  match check_guard guard ms with
  | Some (ms, ns) ->
    List.fold_left (fun acc_opt ((p0s, bnd) as cl) ->
        match acc_opt with
        | Some _ -> acc_opt
        | None -> try Some (psubst cl ms, ns) with _ -> None)
      None cls
  | None -> None

let rec aeq_tm m1 m2 =
  if m1 == m2 then true
  else match (m1, m2) with
    (* inference *)
    | Ann (m1, a1), Ann (m2, a2) -> aeq_tm m1 m2 && aeq_tm a1 a2
    | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
    | PMeta x1, PMeta x2 -> eq_vars x1 x2
    (* core *)
    | Type s1, Type s2 -> eq_sort s1 s2
    | Var x1, Var x2 -> eq_vars x1 x2
    | Const (x1, ss1), Const (x2, ss2) ->
      Const.equal x1 x2 && List.equal eq_sort ss1 ss2
    | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
      relv1 = relv2 && eq_sort s1 s2 && aeq_tm a1 a2
      && eq_binder aeq_tm bnd1 bnd2
    | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
      aeq_tm a1 a2
      && eq_binder (List.equal (eq_pbinder (Option.equal aeq_tm))) bnd1 bnd2
    | App (m1, n1), App (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
      relv1 = relv2 && aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* inductive *)
    | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2) ->
      Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 && List.equal aeq_tm ms1 ms2
      && List.equal aeq_tm ns1 ns2
    | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2) ->
      Constr.equal c1 c2 && List.equal eq_sort ss1 ss2
      && List.equal aeq_tm ms1 ms2 && List.equal aeq_tm ns1 ns2
    | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
      List.equal aeq_tm ms1 ms2 && aeq_tm a1 a2
      && List.equal (eq_pbinder (Option.equal aeq_tm)) cls1 cls2
    (* monad *)
    | IO a1, IO a2 -> aeq_tm a1 a2
    | Return m1, Return m2 -> aeq_tm m1 m2
    | MLet (m1, bnd1), MLet (m2, bnd2) ->
      aeq_tm m1 m2 && eq_binder aeq_tm bnd1 bnd2
    (* primitive types *)
    | Int_t, Int_t -> true
    | Char_t, Char_t -> true
    | String_t, String_t -> true
    (* primitive terms *)
    | Int i1, Int i2 -> i1 = i2
    | Char c1, Char c2 -> c1 = c2
    | String s1, String s2 -> s1 = s2
    (* primitive operators *)
    | Neg m1, Neg m2 -> aeq_tm m1 m2
    | Add (m1, n1), Add (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Sub (m1, n1), Sub (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Mul (m1, n1), Mul (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Div (m1, n1), Div (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Mod (m1, n1), Mod (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Lte (m1, n1), Lte (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Gte (m1, n1), Gte (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Lt (m1, n1), Lt (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Gt (m1, n1), Gt (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Eq (m1, n1), Eq (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Chr m1, Chr m2 -> aeq_tm m1 m2
    | Ord m1, Ord m2 -> aeq_tm m1 m2
    | Push (m1, n1), Push (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Cat (m1, n1), Cat (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    | Size m1, Size m2 -> aeq_tm m1 m2
    | Indx (m1, n1), Indx (m2, n2) -> aeq_tm m1 m2 && aeq_tm n1 n2
    (* primitive sessions *)
    | Proto, Proto -> true
    | End, End -> true
    | Act (relv1, role1, a1, bnd1), Act (relv2, role2, a2, bnd2) ->
      relv1 = relv2 && role1 = role2 && aeq_tm a1 a2 && eq_binder aeq_tm bnd1 bnd2
    | Ch (role1, m1), Ch (role2, m2) -> role1 = role2 && aeq_tm m1 m2
    (* primitive effects *)
    | Print m1, Print m2 -> aeq_tm m1 m2
    | Prerr m1, Prerr m2 -> aeq_tm m1 m2
    | ReadLn m1, ReadLn m2 -> aeq_tm m1 m2
    | Fork m1, Fork m2 -> aeq_tm m1 m2
    | Send m1, Send m2 -> aeq_tm m1 m2
    | Recv m1, Recv m2 -> aeq_tm m1 m2
    | Close m1, Close m2 -> aeq_tm m1 m2
    (* magic *)
    | Magic a1, Magic a2 -> aeq_tm a1 a2
    (* other *)
    | _ -> false

let rec eq_tm ?(expand = false) env m1 m2 =
  let rec equal m1 m2 =
    if aeq_tm m1 m2 then true
    else
      let m1 = whnf ~expand env m1 in
      let m2 = whnf ~expand env m2 in
      match (m1, m2) with
      (* inference *)
      | IMeta (x1, _, _), IMeta (x2, _, _) -> IMeta.equal x1 x2
      | PMeta x1, PMeta x2 -> eq_vars x1 x2
      (* core *)
      | Type s1, Type s2 -> eq_sort s1 s2
      | Var x1, Var x2 -> eq_vars x1 x2
      | Const (x1, ss1), Const (x2, ss2) ->
        Const.equal x1 x2 && List.equal eq_sort ss1 ss2
      | Pi (relv1, s1, a1, bnd1), Pi (relv2, s2, a2, bnd2) ->
        relv1 = relv2 && eq_sort s1 s2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Fun (_, a1, bnd1), Fun (_, a2, bnd2) ->
        equal a1 a2 && eq_binder (List.equal (eq_pbinder (Option.equal equal))) bnd1 bnd2
      | App (m1, n1), App (m2, n2) -> equal m1 m2 && equal n1 n2
      | Let (relv1, m1, bnd1), Let (relv2, m2, bnd2) ->
        relv1 = relv2 && equal m1 m2 && eq_binder equal bnd1 bnd2
      (* inductive *)
      | Ind (d1, ss1, ms1, ns1), Ind (d2, ss2, ms2, ns2) ->
        Ind.equal d1 d2 && List.equal eq_sort ss1 ss2 &&
        List.equal equal ms1 ms2 && List.equal equal ns1 ns2
      | Constr (c1, ss1, ms1, ns1), Constr (c2, ss2, ms2, ns2) ->
        Constr.equal c1 c2 && List.equal eq_sort ss1 ss2 &&
        List.equal equal ms1 ms2 && List.equal equal ns1 ns2
      | Match (_, ms1, a1, cls1), Match (_, ms2, a2, cls2) ->
        List.equal equal ms1 ms2 && equal a1 a2 &&
        List.equal (eq_pbinder (Option.equal equal)) cls1 cls2
      (* monad *)
      | IO a1, IO a2 -> equal a1 a2
      | Return m1, Return m2 -> equal m1 m2
      | MLet (m1, bnd1), MLet (m2, bnd2) ->
        equal m1 m2 && eq_binder equal bnd1 bnd2
      (* primitive types *)
      | Int_t, Int_t -> true
      | Char_t, Char_t -> true
      | String_t, String_t -> true
      (* primitive terms *)
      | Int i1, Int i2 -> i1 = i2
      | Char c1, Char c2 -> c1 = c2
      | String s1, String s2 -> s1 = s2
      (* primitive operators *)
      | Neg m1, Neg m2 -> equal m1 m2
      | Add (m1, n1), Add (m2, n2) -> equal m1 m2 && equal n1 n2
      | Sub (m1, n1), Sub (m2, n2) -> equal m1 m2 && equal n1 n2
      | Mul (m1, n1), Mul (m2, n2) -> equal m1 m2 && equal n1 n2
      | Div (m1, n1), Div (m2, n2) -> equal m1 m2 && equal n1 n2
      | Mod (m1, n1), Mod (m2, n2) -> equal m1 m2 && equal n1 n2
      | Lte (m1, n1), Lte (m2, n2) -> equal m1 m2 && equal n1 n2
      | Gte (m1, n1), Gte (m2, n2) -> equal m1 m2 && equal n1 n2
      | Lt (m1, n1), Lt (m2, n2) -> equal m1 m2 && equal n1 n2
      | Gt (m1, n1), Gt (m2, n2) -> equal m1 m2 && equal n1 n2
      | Eq (m1, n1), Eq (m2, n2) -> equal m1 m2 && equal n1 n2
      | Chr m1, Chr m2 -> equal m1 m2
      | Ord m1, Ord m2 -> equal m1 m2
      | Push (m1, n1), Push (m2, n2) -> equal m1 m2 && equal n1 n2
      | Cat (m1, n1), Cat (m2, n2) -> equal m1 m2 && equal n1 n2
      | Size m1, Size m2 -> equal m1 m2
      | Indx (m1, n1), Indx (m2, n2) -> equal m1 m2 && equal n1 n2
      (* primitive sessions *)
      | Proto, Proto -> true
      | End, End -> true
      | Act (relv1, role1, a1, bnd1), Act (relv2, role2, a2, bnd2) ->
        relv1 = relv2 && role1 = role2 && equal a1 a2 && eq_binder equal bnd1 bnd2
      | Ch (role1, m1), Ch (role2, m2) -> role1 = role2 && equal m1 m2
      (* primitive effects *)
      | Print m1, Print m2 -> equal m1 m2
      | Prerr m1, Prerr m2 -> equal m1 m2
      | ReadLn m1, ReadLn m2 -> equal m1 m2
      | Fork m1, Fork m2 -> equal m1 m2
      | Send m1, Send m2 -> equal m1 m2
      | Recv m1, Recv m2 -> equal m1 m2
      | Close m1, Close m2 -> equal m1 m2
      (* magic *)
      | Magic a1, Magic a2 -> equal a1 a2
      (* other *)
      | _ -> false
  in
  if equal m1 m2 then true
  else if expand then false
  else eq_tm ~expand:true env m1 m2
