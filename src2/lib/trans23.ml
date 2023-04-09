open Fmt
open Bindlib
open Names
open Trans12
open Syntax2

type 'a trans23 = int IMap.t * Resolver.t -> 'a

let return m : 'a trans23 = fun arity -> m

let ( >>= ) (m : 'a trans23) (f : 'a -> 'b trans23) : 'b trans23 =
 fun arity -> f (m arity) arity

let ( let* ) = ( >>= )
let get_arity x : int trans23 = fun (arity, _) -> IMap.find x arity
let resolve_c c : C.t trans23 = fun (_, res) -> Resolver.find_cons c [] res

let set_arity x i (m : 'a trans23) : 'a trans23 =
 fun (arity, res) -> m (IMap.add x i arity, res)

let rec mapM (f : 'a -> 'b trans23) (xs : 'a list) : 'b list trans23 =
  match xs with
  | [] -> return []
  | x :: xs ->
    let* x = f x in
    let* xs = mapM f xs in
    return (x :: xs)

let rec foldM xs acc f : 'b trans23 =
  match xs with
  | [] -> return acc
  | x :: xs ->
    let* acc = f x acc in
    foldM xs acc f

let trans_sort = function
  | U -> Syntax3.U
  | L -> Syntax3.L

let trans_prim = function
  | Stdin -> Syntax3.Stdin
  | Stdout -> Syntax3.Stdout
  | Stderr -> Syntax3.Stderr

let trans_var x = Syntax3.(copy_var x var (name_of x))
let trans_mvar xs = Array.map trans_var xs

let rec gather_mlet = function
  | MLet (m, bnd) ->
    let x, n = unbind bnd in
    let xs, n = gather_mlet n in
    ((x, m) :: xs, n)
  | m -> ([], m)

let rec trans_tm = function
  | Var x -> return Syntax3.(_Var (trans_var x))
  | Const x -> return Syntax3.(_Const x)
  | Lam (s, bnd) ->
    let x, m = unbind bnd in
    let* m = trans_tm m in
    let bnd = bind_var (trans_var x) m in
    return Syntax3.(_Lam (trans_sort s) bnd)
  | App (s, m, n) as tm -> (
    let hd, sp = unApps tm in
    match hd with
    | Const x ->
      let* i = get_arity x in
      if i = List.length sp then
        let* sp = mapM trans_tm sp in
        return Syntax3.(_Call x (box_list sp))
      else
        let* m = trans_tm m in
        let* n = trans_tm n in
        return Syntax3.(_App (trans_sort s) m n)
    | _ ->
      let* m = trans_tm m in
      let* n = trans_tm n in
      return Syntax3.(_App (trans_sort s) m n))
  | Let (m, bnd) ->
    let x, n = unbind bnd in
    let* m = trans_tm m in
    let* n = trans_tm n in
    let bnd = bind_var (trans_var x) n in
    return Syntax3.(_Let m bnd)
  (* data *)
  | Pair (m, n) ->
    let* m = trans_tm m in
    let* n = trans_tm n in
    return Syntax3.(_Pair m n)
  | Cons (c, ms) ->
    let* ms = mapM trans_tm ms in
    return Syntax3.(_Cons c (box_list ms))
  | Match (s, m, cls) ->
    let s = trans_sort s in
    let* m = trans_tm m in
    let* cls =
      mapM
        (function
          | PPair bnd ->
            let xs, rhs = unmbind bnd in
            let* rhs = trans_tm rhs in
            let bnd = bind_mvar (trans_mvar xs) rhs in
            return Syntax3.(_PPair bnd)
          | PCons (c, bnd) ->
            let xs, rhs = unmbind bnd in
            let* rhs = trans_tm rhs in
            let bnd = bind_mvar (trans_mvar xs) rhs in
            return Syntax3.(_PCons c bnd))
        cls
    in
    return Syntax3.(_Match s m (box_list cls))
  (* monadic *)
  | Return m ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = bind_var arg m in
    return Syntax3.(_Lam L bnd)
  | MLet _ as m ->
    let arg = Syntax3.(V.mk "_") in
    let xs, n = gather_mlet m in
    let* n = trans_tm n in
    let* m =
      foldM xs
        Syntax3.(_App L n _NULL)
        (fun (x, m) acc ->
          let x = trans_var x in
          let* m = trans_tm m in
          let bnd = Syntax3.(bind_var x acc) in
          return Syntax3.(_Let (_App L m _NULL) bnd))
    in
    let bnd = bind_var arg m in
    return Syntax3.(_Lam L bnd)
  (* session *)
  | Open prim ->
    let arg = Syntax3.(V.mk "_") in
    let prim = trans_prim prim in
    let bnd = Syntax3.(bind_var arg (_Open prim)) in
    return Syntax3.(_Lam L bnd)
  | Fork bnd ->
    let arg = Syntax3.(V.mk "_") in
    let x, m = unbind bnd in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var (trans_var x) (_App L m _NULL)) in
    let bnd = Syntax3.(bind_var arg (_Fork bnd)) in
    return Syntax3.(_Lam L bnd)
  | Recv (R, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Recv m)) in
    return Syntax3.(_Lam L bnd)
  | Recv (N, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Pair _NULL m)) in
    return Syntax3.(_Lam L bnd)
  | Send (R, s, m) ->
    let arg = Syntax3.(V.mk "_") in
    let x = Syntax3.(V.mk "x") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var x (_Send m (_Var x))) in
    let bnd = Syntax3.(bind_var arg (_Lam (trans_sort s) bnd)) in
    return Syntax3.(_Lam L bnd)
  | Send (N, s, m) ->
    let arg = Syntax3.(V.mk "_") in
    let x = Syntax3.(V.mk "x") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var x m) in
    let bnd = Syntax3.(bind_var arg (_Lam (trans_sort s) bnd)) in
    return Syntax3.(_Lam L bnd)
  | Close (Pos, m) ->
    let arg = Syntax3.(V.mk "_") in
    let x = Syntax3.(V.mk "x") in
    let* m = trans_tm m in
    let* c = resolve_c Prelude1.tt_c in
    let bnd = Syntax3.(bind_var x (_Cons c (box []))) in
    let bnd = Syntax3.(bind_var arg (_Let m bnd)) in
    return Syntax3.(_Lam L bnd)
  | Close (Neg, m) ->
    let arg = Syntax3.(V.mk "_") in
    let* m = trans_tm m in
    let bnd = Syntax3.(bind_var arg (_Close m)) in
    return Syntax3.(_Lam L bnd)
  (* erasure *)
  | NULL -> return Syntax3._NULL
