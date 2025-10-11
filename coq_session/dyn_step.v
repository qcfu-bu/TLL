From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Inductive dyn_thunk : term -> Prop :=
| dyn_thunk_bind m n : dyn_thunk m -> dyn_thunk (Bind m n)
| dyn_thunk_fork A m : dyn_thunk (Fork A m)
| dyn_thunk_recv0 v  : dyn_val v -> dyn_thunk (Recv0 v)
| dyn_thunk_recv1 v  : dyn_val v -> dyn_thunk (Recv1 v)
| dyn_thunk_send0_app v m :
  dyn_val v ->
  dyn_thunk (App0 (Send0 v) m)
| dyn_thunk_send1_app v1 v2  :
  dyn_val v1 ->
  dyn_val v2 ->
  dyn_thunk (App1 (Send1 v1) v2)
| dyn_thunk_close v  : dyn_val v -> dyn_thunk (Close v)
| dyn_thunk_wait v   : dyn_val v -> dyn_thunk (Wait v)

with dyn_val : term -> Prop :=
| dyn_val_var x : dyn_val (Var x)
| dyn_val_lam0 A m s : dyn_val (Lam0 A m s)
| dyn_val_lam1 A m s : dyn_val (Lam1 A m s)
| dyn_val_pair0 m1 m2 s :
  dyn_val m2 ->
  dyn_val (Pair0 m1 m2 s)
| dyn_val_pair1 m1 m2 s :
  dyn_val m1 ->
  dyn_val m2 ->
  dyn_val (Pair1 m1 m2 s)
| dyn_val_ii : dyn_val II
| dyn_val_tt : dyn_val TT
| dyn_val_ff : dyn_val FF
| dyn_val_return v : dyn_val v -> dyn_val (Return v)
| dyn_val_cvar x   : dyn_val (CVar x)
| dyn_val_send0 v  : dyn_val v -> dyn_val (Send0 v)
| dyn_val_send1 v  : dyn_val v -> dyn_val (Send1 v)
| dyn_val_thunk m  : dyn_thunk m -> dyn_val m.

Scheme dyn_thunk_mut := Induction for dyn_thunk Sort Prop
with dyn_val_mut := Induction for dyn_val Sort Prop.

Reserved Notation "m ~>> n" (at level 50).
Inductive dyn_step : term -> term -> Prop :=
(* core *)
| dyn_step_app0L m m' n :
  m ~>> m' ->
  App0 m n ~>> App0 m' n
| dyn_step_app1L m m' n :
  m ~>> m' ->
  App1 m n ~>> App1 m' n
| dyn_step_app1R m n n' :
  n ~>> n' ->
  App1 m n ~>> App1 m n'
| dyn_step_beta0 A m n s :
  App0 (Lam0 A m s) n ~>> m.[n/]
| dyn_step_beta1 A m v s :
  dyn_val v ->
  App1 (Lam1 A m s) v ~>> m.[v/]
| dyn_step_pair0R m n n' s :
  n ~>> n' ->
  Pair0 m n s ~>> Pair0 m n' s
| dyn_step_pair1L m m' n s :
  m ~>> m' ->
  Pair1 m n s ~>> Pair1 m' n s
| dyn_step_pair1R m n n' s :
  n ~>> n' ->
  Pair1 m n s ~>> Pair1 m n' s
| dyn_step_letinL A m m' n :
  m ~>> m' ->
  LetIn A m n ~>> LetIn A m' n
| dyn_step_letinE0 A m1 m2 n s :
  dyn_val (Pair0 m1 m2 s) ->
  LetIn A (Pair0 m1 m2 s) n ~>> n.[m2,m1/]
| dyn_step_letinE1 A m1 m2 n s :
  dyn_val (Pair1 m1 m2 s) ->
  LetIn A (Pair1 m1 m2 s) n ~>> n.[m2,m1/]
| dyn_step_fixE A m :
  Fix A m ~>> m.[Fix A m/]
(* data *)
| dyn_step_ifteM A m m' n1 n2 :
  m ~>> m' ->
  Ifte A m n1 n2 ~>> Ifte A m' n1 n2
| dyn_step_ifteT A n1 n2 :
  Ifte A TT n1 n2 ~>> n1
| dyn_step_ifteF A n1 n2 :
  Ifte A FF n1 n2 ~>> n2
(* monadic *)
| dyn_step_return m m' :
  m ~>> m' ->
  Return m ~>> Return m'
| dyn_step_bindL m m' n :
  m ~>> m' ->
  Bind m n ~>> Bind m' n
| dyn_step_bindE v n : 
  dyn_val v ->
  Bind (Return v) n ~>> n.[v/]
(* session *)
| dyn_step_recv0 m m' :
  m ~>> m' ->
  Recv0 m ~>> Recv0 m'
| dyn_step_recv1 m m' :
  m ~>> m' ->
  Recv1 m ~>> Recv1 m'
| dyn_step_send0 m m' :
  m ~>> m' ->
  Send0 m ~>> Send0 m'
| dyn_step_send1 m m' :
  m ~>> m' ->
  Send1 m ~>> Send1 m'
| dyn_step_close m m' :
  m ~>> m' ->
  Close m ~>> Close m'
| dyn_step_wait m m' :
  m ~>> m' ->
  Wait m ~>> Wait m'
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 50).
