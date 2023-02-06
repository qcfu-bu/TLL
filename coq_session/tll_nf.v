From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive nf : nat -> term -> Prop :=
(* core *)
| nf_var i x :
  x < i ->
  nf i (Var x)
| nf_sort i s :
  nf i (Sort s)
| nf_pi0 i A B s :
  nf i A ->
  nf i.+1 B ->
  nf i (Pi0 A B s)
| nf_pi1 i A B s :
  nf i A ->
  nf i.+1 B ->
  nf i (Pi1 A B s)
| nf_lam0 i A m s :
  nf i A ->
  nf i.+1 m ->
  nf i (Lam0 A m s)
| nf_lam1 i A m s :
  nf i A ->
  nf i.+1 m ->
  nf i (Lam0 A m s)
| nf_app i m n :
  nf i m ->
  nf i n ->
  nf i (App m n)
| nf_sig0 i A B s :
  nf i A ->
  nf i.+1 B ->
  nf i (Sig0 A B s)
| nf_sig1 i A B s :
  nf i A ->
  nf i.+1 B ->
  nf i (Sig1 A B s)
| nf_pair0 i m n s :
  nf i m ->
  nf i n ->
  nf i (Pair0 m n s)
| nf_pair1 i m n s :
  nf i m ->
  nf i n ->
  nf i (Pair1 m n s)
| nf_letin i A m n :
  nf i.+1 A ->
  nf i m ->
  nf i.+2 n ->
  nf i (LetIn A m n)
| nf_fix i A m :
  nf i A ->
  nf i.+1 m ->
  nf i (Fix A m)
(* data *)
| nf_unit i : nf i Unit
| nf_ii i : nf i II
| nf_bool i : nf i Bool
| nf_tt i : nf i TT
| nf_ff i : nf i FF
| nf_ifte i A m n1 n2 :
  nf i.+1 A ->
  nf i m ->
  nf i n1 ->
  nf i n2 ->
  nf i (Ifte A m n1 n2)
(* monadic *)
| nf_io i A :
  nf i A ->
  nf i (IO A)
| nf_return i m :
  nf i m ->
  nf i (Return m)
| nf_bind i m n :
  nf i m ->
  nf i.+1 n ->
  nf i (Bind m n)
(* session *)
| nf_proto i : nf i Proto
| nf_stop i r : nf i (Stop r)
| nf_act0 i r A B :
  nf i A ->
  nf i.+1 B ->
  nf i (Act0 r A B)
| nf_act1 i r A B :
  nf i A ->
  nf i.+1 B ->
  nf i (Act1 r A B)
| nf_ch i r A :
  nf i A ->
  nf i (Ch r A)
| nf_cvar i x : nf i (CVar x)
| nf_fork i A m :
  nf i A ->
  nf i.+1 m ->
  nf i (Fork A m)
| nf_recv i m :
  nf i m ->
  nf i (Recv m)
| nf_send i m :
  nf i m ->
  nf i (Send m)
| nf_close i m :
  nf i m ->
  nf i (Close m)
| nf_wait i m :
  nf i m ->
  nf i (Wait m).

Definition id_ren i ξ := forall x, x < i -> ξ x = x.

Lemma id_ren1 : id_ren 0 (+1).
Proof. move=>x h. inv h. Qed.

Lemma id_ren_up i ξ : id_ren i ξ -> id_ren i.+1 (upren ξ).
Proof.
  move=>idr x h.
  destruct x.
  asimpl. eauto.
  asimpl. rewrite idr; eauto.
Qed.

Lemma nf_id_ren i m ξ : nf i m -> id_ren i ξ -> m = m.[ren ξ].
Proof with eauto using id_ren_up.
  move=>nfi. elim: nfi ξ=>{i m}...
  { move=>i x lt ξ idr. asimpl. rewrite idr... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A m s nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i A m s nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i m n nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i m n s nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i m n s nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i A m n nfA ihA nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm...
    have eq:=ihn _ (id_ren_up (id_ren_up idr)).
    asimpl in eq. rewrite<-eq... }
  { move=>i A m nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i A m n1 n2 nfA ihA nfm ihm nfn1 ihn1 nfn2 ihn2 ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm...
    rewrite<-ihn1... rewrite<-ihn2... }
  { move=>i A nfA ihA ξ idr. asimpl. rewrite<-ihA... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m n nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i r A B nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i r A B nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i r A nfA ihA ξ idr. asimpl. rewrite<-ihA... }
  { move=>i A m nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
Qed.

Definition id_subst i σ := forall x, x < i -> σ x = Var x.

Lemma id_subst_up i σ : id_subst i σ -> id_subst i.+1 (up σ).
Proof.
  move=>idr x h.
  destruct x.
  asimpl. eauto.
  asimpl. rewrite idr; eauto.
Qed.

Lemma nf_id_subst i m σ : nf i m -> id_subst i σ -> m = m.[σ].
Proof with eauto using id_subst_up.
  move=>nfi. elim: nfi σ=>{i m}...
  { move=>i x lt ξ idr. asimpl. rewrite idr... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A m s nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i A m s nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i m n nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i A B s nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i m n s nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i m n s nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i A m n nfA ihA nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm...
    have eq:=ihn _ (id_subst_up (id_subst_up idr)).
    asimpl in eq. rewrite<-eq... }
  { move=>i A m nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i A m n1 n2 nfA ihA nfm ihm nfn1 ihn1 nfn2 ihn2 ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm...
    rewrite<-ihn1... rewrite<-ihn2... }
  { move=>i A nfA ihA ξ idr. asimpl. rewrite<-ihA... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m n nfm ihm nfn ihn ξ idr. asimpl.
    rewrite<-ihm... rewrite<-ihn... }
  { move=>i r A B nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i r A B nfA ihA nfB ihB ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihB... }
  { move=>i r A nfA ihA ξ idr. asimpl. rewrite<-ihA... }
  { move=>i A m nfA ihA nfm ihm ξ idr. asimpl.
    rewrite<-ihA... rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. asimpl. rewrite<-ihm... }
Qed.
