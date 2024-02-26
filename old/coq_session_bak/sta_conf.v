From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "m ≈> n" (at level 50).
Inductive sta_pstep : term -> term -> Prop :=
(* core *)
| sta_pstep_var x :
  Var x ≈> Var x
| sta_pstep_sort s :
  Sort s ≈> Sort s
| sta_pstep_pi0 A A' B B' s :
  A ≈> A' ->
  B ≈> B' ->
  Pi0 A B s ≈> Pi0 A' B' s
| sta_pstep_pi1 A A' B B' s :
  A ≈> A' ->
  B ≈> B' ->
  Pi1 A B s ≈> Pi1 A' B' s
| sta_pstep_lam0 A A' m m' s :
  A ≈> A' ->
  m ≈> m' ->
  Lam0 A m s ≈> Lam0 A' m' s
| sta_pstep_lam1 A A' m m' s :
  A ≈> A' ->
  m ≈> m' ->
  Lam1 A m s ≈> Lam1 A' m' s
| sta_pstep_app0 m m' n n' :
  m ≈> m' ->
  n ≈> n' ->
  App0 m n ≈> App0 m' n'
| sta_pstep_app1 m m' n n' :
  m ≈> m' ->
  n ≈> n' ->
  App1 m n ≈> App1 m' n'
| sta_pstep_beta0 A m m' n n' s :
  m ≈> m' ->
  n ≈> n' ->
  App0 (Lam0 A m s) n ≈> m'.[n'/]
| sta_pstep_beta1 A m m' n n' s :
  m ≈> m' ->
  n ≈> n' ->
  App1 (Lam1 A m s) n ≈> m'.[n'/]
| sta_pstep_sig0 A A' B B' s :
  A ≈> A' ->
  B ≈> B' ->
  Sig0 A B s ≈> Sig0 A' B' s
| sta_pstep_sig1 A A' B B' s :
  A ≈> A' ->
  B ≈> B' ->
  Sig1 A B s ≈> Sig1 A' B' s
| sta_pstep_pair0 m m' n n' s :
  m ≈> m' ->
  n ≈> n' ->
  Pair0 m n s ≈> Pair0 m' n' s
| sta_pstep_pair1 m m' n n' s :
  m ≈> m' ->
  n ≈> n' ->
  Pair1 m n s ≈> Pair1 m' n' s
| sta_pstep_letin A A' m m' n n' :
  A ≈> A' ->
  m ≈> m' ->
  n ≈> n' ->
  LetIn A m n ≈> LetIn A' m' n'
| sta_pstep_letinE0 A m1 m1' m2 m2' n n' s :
  m1 ≈> m1' ->
  m2 ≈> m2' ->
  n ≈> n' ->
  LetIn A (Pair0 m1 m2 s) n ≈> n'.[m2',m1'/]
| sta_pstep_letinE1 A m1 m1' m2 m2' n n' s :
  m1 ≈> m1' ->
  m2 ≈> m2' ->
  n ≈> n' ->
  LetIn A (Pair1 m1 m2 s) n ≈> n'.[m2',m1'/]
| sta_pstep_fix A A' m m' :
  A ≈> A' ->
  m ≈> m' ->
  Fix A m ≈> Fix A' m'
| sta_pstep_fixE A A' m m' :
  A ≈> A' ->
  m ≈> m' ->
  Fix A m ≈> m'.[Fix A' m'/]
(* data *)
| sta_pstep_unit : Unit ≈> Unit
| sta_pstep_ii : II ≈> II
| sta_pstep_bool : Bool ≈> Bool
| sta_pstep_tt : TT ≈> TT
| sta_pstep_ff : FF ≈> FF
| sta_pstep_ifte A A' m m' n1 n1' n2 n2' : 
  A ≈> A' ->
  m ≈> m' ->
  n1 ≈> n1' ->
  n2 ≈> n2' ->
  Ifte A m n1 n2 ≈> Ifte A' m' n1' n2'
| sta_pstep_ifteT A n1 n1' n2 :
  n1 ≈> n1' ->
  Ifte A TT n1 n2 ≈> n1'
| sta_pstep_ifteF A n1 n2 n2' :
  n2 ≈> n2' ->
  Ifte A FF n1 n2 ≈> n2'
(* monadic *)
| sta_pstep_io A A' :
  A ≈> A' ->
  IO A ≈> IO A'
| sta_pstep_return m m' :
  m ≈> m' ->
  Return m ≈> Return m'
| sta_pstep_bind m m' n n' :
  m ≈> m' ->
  n ≈> n' ->
  Bind m n ≈> Bind m' n'
| sta_pstep_bindE m m' n n' :
  m ≈> m' ->
  n ≈> n' ->
  Bind (Return m) n ≈> n'.[m'/]
(* session *) 
| sta_pstep_proto : Proto ≈> Proto
| sta_pstep_stop : Stop ≈> Stop
| sta_pstep_act0 r A A' B B' :
  A ≈> A' ->
  B ≈> B' ->
  Act0 r A B ≈> Act0 r A' B'
| sta_pstep_act1 r A A' B B' :
  A ≈> A' ->
  B ≈> B' ->
  Act1 r A B ≈> Act1 r A' B'
| sta_pstep_ch r A A' :
  A ≈> A' ->
  Ch r A ≈> Ch r A'
| sta_pstep_cvar x y :
  CVar x ≈> CVar y
| sta_pstep_fork A A' m m' :
  A ≈> A' ->
  m ≈> m' ->
  Fork A m ≈> Fork A' m'
| sta_pstep_recv0 m m' :
  m ≈> m' ->
  Recv0 m ≈> Recv0 m'
| sta_pstep_recv1 m m' :
  m ≈> m' ->
  Recv1 m ≈> Recv1 m'
| sta_pstep_send0 m m' :
  m ≈> m' ->
  Send0 m ≈> Send0 m'
| sta_pstep_send1 m m' :
  m ≈> m' ->
  Send1 m ≈> Send1 m'
| sta_pstep_close m m' :
  m ≈> m' ->
  Close m ≈> Close m'
| sta_pstep_wait m m' :
  m ≈> m' ->
  Wait m ≈> Wait m'
where "m ≈> n" := (sta_pstep m n).

Notation sta_pred := (star sta_pstep).
Notation "m ≈>* n" := (sta_pred m n) (at level 50).
Notation "m === n" := (conv sta_pstep m n) (at level 50).

Definition sred σ τ := forall x : var, (σ x) ~>* (τ x).

Lemma sta_step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using sta_step.
  { move=>A m n s σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_beta0. autosubst. }
  { move=>A m n s σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_beta1. autosubst. }
  { move=>A m1 m2 n s σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/]).
    apply: sta_step_letinE0. autosubst. }
  { move=>A m1 m2 n s σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/]).
    apply: sta_step_letinE1. autosubst. }
  { move=>A m σ.
    replace (m.[Fix A m/].[σ]) with (m.[up σ].[(Fix A m).[σ]/]).
    apply: sta_step_fixE. autosubst. }
  { move=>m n σ.
    replace (n.[m/].[σ]) with (n.[up σ].[m.[σ]/]).
    apply: sta_step_bindE. autosubst. }
Qed.

Lemma sta_red_pi0 A A' B B' s :
  A ~>* A' -> B ~>* B' -> Pi0 A B s ~>* Pi0 A' B' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi0 A' B s)).
  apply: (star_hom ((Pi0^~ B)^~ s)) r1=>x y. exact: sta_step_pi0L.
  apply: (star_hom ((Pi0 A')^~ s)) r2=>x y. exact: sta_step_pi0R.
Qed.

Lemma sta_red_pi1 A A' B B' s :
  A ~>* A' -> B ~>* B' -> Pi1 A B s ~>* Pi1 A' B' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi1 A' B s)).
  apply: (star_hom ((Pi1^~ B)^~ s)) r1=>x y. exact: sta_step_pi1L.
  apply: (star_hom ((Pi1 A')^~ s)) r2=>x y. exact: sta_step_pi1R.
Qed.

Lemma sta_red_lam0 A A' m m' s :
  A ~>* A' -> m ~>* m' -> Lam0 A m s ~>* Lam0 A' m' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam0 A' m s)).
  apply: (star_hom ((Lam0^~ m)^~ s)) r1=>x y. exact: sta_step_lam0L.
  apply: (star_hom ((Lam0 A')^~ s)) r2=>x y. exact: sta_step_lam0R.
Qed.

Lemma sta_red_lam1 A A' m m' s :
  A ~>* A' -> m ~>* m' -> Lam1 A m s ~>* Lam1 A' m' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam1 A' m s)).
  apply: (star_hom ((Lam1^~ m)^~ s)) r1=>x y. exact: sta_step_lam1L.
  apply: (star_hom ((Lam1 A')^~ s)) r2=>x y. exact: sta_step_lam1R.
Qed.

Lemma sta_red_app0 m m' n n' :
  m ~>* m' -> n ~>* n' -> App0 m n ~>* App0 m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App0 m' n)).
  apply: (star_hom (App0^~ n)) r1=>x y. exact: sta_step_app0L.
  apply: star_hom r2. exact: sta_step_app0R.
Qed.

Lemma sta_red_app1 m m' n n' :
  m ~>* m' -> n ~>* n' -> App1 m n ~>* App1 m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App1 m' n)).
  apply: (star_hom (App1^~ n)) r1=>x y. exact: sta_step_app1L.
  apply: star_hom r2. exact: sta_step_app1R.
Qed.

Lemma sta_red_sig0 A A' B B' s :
  A ~>* A' -> B ~>* B' -> Sig0 A B s ~>* Sig0 A' B' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Sig0 A' B s)).
  apply: (star_hom ((Sig0^~ B)^~ s)) r1=>x y. exact: sta_step_sig0L.
  apply: (star_hom ((Sig0 A')^~ s)) r2=>x y. exact: sta_step_sig0R.
Qed.

Lemma sta_red_sig1 A A' B B' s :
  A ~>* A' -> B ~>* B' -> Sig1 A B s ~>* Sig1 A' B' s.
Proof.
  move=> r1 r2.
  apply: (star_trans (Sig1 A' B s)).
  apply: (star_hom ((Sig1^~ B)^~ s)) r1=>x y. exact: sta_step_sig1L.
  apply: (star_hom ((Sig1 A')^~ s)) r2=>x y. exact: sta_step_sig1R.
Qed.

Lemma sta_red_pair0 m m' n n' t :
  m ~>* m' -> n ~>* n' -> Pair0 m n t ~>* Pair0 m' n' t.
Proof.
  move=>r1 r2.
  apply: (star_trans (Pair0 m' n t)).
  apply: (star_hom ((Pair0^~ n)^~ t)) r1=>x y. exact: sta_step_pair0L.
  apply: (star_hom ((Pair0 m')^~ t)) r2=>x y. exact: sta_step_pair0R.
Qed.

Lemma sta_red_pair1 m m' n n' t :
  m ~>* m' -> n ~>* n' -> Pair1 m n t ~>* Pair1 m' n' t.
Proof.
  move=>r1 r2.
  apply: (star_trans (Pair1 m' n t)).
  apply: (star_hom ((Pair1^~ n)^~ t)) r1=>x y. exact: sta_step_pair1L.
  apply: (star_hom ((Pair1 m')^~ t)) r2=>x y. exact: sta_step_pair1R.
Qed.

Lemma sta_red_letin A A' m m' n n' :
  A ~>* A' -> m ~>* m' -> n ~>* n' -> LetIn A m n ~>* LetIn A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (LetIn A' m n)).
  apply: (star_hom ((LetIn^~ m)^~ n)) r1=>x y. exact: sta_step_letinA.
  apply: (star_trans (LetIn A' m' n)).
  apply: (star_hom (LetIn A'^~ n)) r2=>x y. exact: sta_step_letinL.
  apply: (star_hom (LetIn A' m')) r3=>x y. exact: sta_step_letinR.
Qed.

Lemma sta_red_fix A A' m m' :
  A ~>* A' -> m ~>* m' -> Fix A m ~>* Fix A' m'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Fix A' m)).
  apply: (star_hom (Fix^~ m)) r1=>x y. exact: sta_step_fixL.
  apply: (star_hom (Fix A')) r2=>x y. exact: sta_step_fixR.
Qed.

Lemma sta_red_ifte A A' m m' n1 n1' n2 n2' :
  A ~>* A' -> m ~>* m' -> n1 ~>* n1' -> n2 ~>* n2' ->
  Ifte A m n1 n2 ~>* Ifte A' m' n1' n2'.
Proof.
  move=> r1 r2 r3 r4.
  apply: (star_trans (Ifte A' m n1 n2)).
  apply: (star_hom (((Ifte^~ m)^~ n1)^~ n2)) r1=>x y. exact: sta_step_ifteA.
  apply: (star_trans (Ifte A' m' n1 n2)).
  apply: (star_hom (((Ifte A')^~ n1)^~ n2)) r2=>x y. exact: sta_step_ifteM.
  apply: (star_trans (Ifte A' m' n1' n2)).
  apply: (star_hom ((Ifte A' m')^~ n2)) r3=>x y. exact: sta_step_ifteN1.
  apply: (star_hom (Ifte A' m' n1')) r4=>x y. exact: sta_step_ifteN2.
Qed.

Lemma sta_red_io A A' : A ~>* A' -> IO A ~>* IO A'.
Proof. move=>r. apply: (star_hom IO) r=>x y. exact: sta_step_io. Qed.

Lemma sta_red_return m m' : m ~>* m' -> Return m ~>* Return m'.
Proof. move=>r. apply: (star_hom Return) r=>x y. exact: sta_step_return. Qed.

Lemma sta_red_bind m m' n n' :
  m ~>* m' -> n ~>* n' -> Bind m n ~>* Bind m' n'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Bind m' n)).
  apply: (star_hom (Bind^~ n)) r1=>x y. exact: sta_step_bindL.
  apply: (star_hom (Bind m')) r2=>x y. exact: sta_step_bindR.
Qed.

Lemma sta_red_act0 r A A' B B' :
  A ~>* A' -> B ~>* B' -> Act0 r A B ~>* Act0 r A' B'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Act0 r A' B)).
  apply: (star_hom (Act0 r ^~ B)) r1=>x y. exact: sta_step_act0L.
  apply: (star_hom (Act0 r A')) r2=>x y. exact: sta_step_act0R.
Qed.

Lemma sta_red_act1 r A A' B B' :
  A ~>* A' -> B ~>* B' -> Act1 r A B ~>* Act1 r A' B'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Act1 r A' B)).
  apply: (star_hom (Act1 r ^~ B)) r1=>x y. exact: sta_step_act1L.
  apply: (star_hom (Act1 r A')) r2=>x y. exact: sta_step_act1R.
Qed.

Lemma sta_red_ch r A A' :
  A ~>* A' -> Ch r A ~>* Ch r A'.
Proof.
  move=>c. apply: (star_hom (Ch r)) c=>x y. exact: sta_step_ch.
Qed.

Lemma sta_red_fork A A' m m' :
  A ~>* A' -> m ~>* m' ->  Fork A m ~>* Fork A' m'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Fork A' m)).
  apply: (star_hom (Fork^~ m)) r1=>x y. exact: sta_step_forkL.
  apply: (star_hom (Fork A')) r2=>x y. exact: sta_step_forkR.
Qed.

Lemma sta_red_recv0 m m' :
  m ~>* m' -> Recv0 m ~>* Recv0 m'.
Proof. move=>r. apply: (star_hom Recv0) r=>x y. exact: sta_step_recv0. Qed.

Lemma sta_red_recv1 m m' :
  m ~>* m' -> Recv1 m ~>* Recv1 m'.
Proof. move=>r. apply: (star_hom Recv1) r=>x y. exact: sta_step_recv1. Qed.

Lemma sta_red_send0 m m' :
  m ~>* m' -> Send0 m ~>* Send0 m'.
Proof. move=>r. apply: (star_hom Send0) r=>x y. exact: sta_step_send0. Qed.

Lemma sta_red_send1 m m' :
  m ~>* m' -> Send1 m ~>* Send1 m'.
Proof. move=>r. apply: (star_hom Send1) r=>x y. exact: sta_step_send1. Qed.

Lemma sta_red_close m m' :
  m ~>* m' -> Close m ~>* Close m'.
Proof. move=>r. apply: (star_hom Close) r=>x y. exact: sta_step_close. Qed.

Lemma sta_red_wait m m' :
  m ~>* m' -> Wait m ~>* Wait m'.
Proof. move=>r. apply: (star_hom Wait) r=>x y. exact: sta_step_wait. Qed.

Lemma sta_red_subst m n σ : m ~>* n -> m.[σ] ~>* n.[σ].
Proof.
  move=>st.
  elim: st σ=>{n}; eauto.
  move=> n n' r ih st σ.
  move:(ih σ)=>{}ih.
  move:(sta_step_subst σ st)=>r'.
  apply: star_trans.
  apply: ih.
  by apply: star1.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: sta_red_subst. exact: A. Qed.

Lemma sred_upn n σ τ : sred σ τ -> sred (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sred_up. by asimpl.
Qed.

#[export] Hint Resolve
  sta_red_pi0 sta_red_pi1
  sta_red_lam0 sta_red_lam1
  sta_red_app0 sta_red_app1
  sta_red_sig0 sta_red_sig1
  sta_red_pair0 sta_red_pair1 sta_red_letin
  sta_red_fix sta_red_ifte
  sta_red_io sta_red_return sta_red_bind
  sta_red_act0 sta_red_act1 sta_red_ch
  sta_red_fork
  sta_red_recv0 sta_red_send0
  sta_red_recv1 sta_red_send1
  sta_red_close sta_red_wait
  sred_up sred_upn : sta_red_congr.

Lemma sta_red_compat σ τ s : sred σ τ -> sta_red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 8 with sta_red_congr. Qed.

Lemma sta_pstep_refl m : m ≈> m.
Proof. elim: m; eauto using sta_pstep. Qed.
#[global] Hint Resolve sta_pstep_refl.

Lemma sta_step_pstep m m' : m ~> m' -> m ≈> m'.
Proof with eauto using sta_pstep, sta_pstep_refl. elim... Qed.

Lemma sta_red_pred m m' : m ~>* m' -> m ≈>* m'.
Proof with eauto using sta_pstep, sta_pstep_refl.
  elim=>{m'}...
  move=>y z rd prd st.
  apply: star_trans...
  apply: star1.
  by apply: sta_step_pstep.
Qed.

Lemma sta_pstep_subst m n σ : m ≈> n -> m.[σ] ≈> n.[σ].
Proof with eauto using sta_pstep, sta_pstep_refl.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' s ps1 ih1 ps2 ih2 σ. asimpl.
    pose proof (sta_pstep_beta0 A.[σ] s (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m m' n n' s ps1 ih1 ps2 ih2 σ. asimpl.
    pose proof (sta_pstep_beta1 A.[σ] s (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ. asimpl.
    pose proof (sta_pstep_letinE0 A.[up σ] s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ. asimpl.
    pose proof (sta_pstep_letinE1 A.[up σ] s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))).
    by asimpl in H. }
  { move=>A A' m m' ps1 ih1 ps2 ih2 σ. asimpl.
    replace (m'.[Fix A'.[σ] m'.[up σ] .: σ])
      with (m'.[up σ].[Fix A'.[σ] m'.[up σ]/])
      by autosubst.
    constructor... }
  { move=>m m' n n' ps1 ih1 ps2 ih2 σ. asimpl.
    pose proof (sta_pstep_bindE (ih1 σ) (ih2 (up σ))) as H.
    by asimpl in H. }
Qed.

Lemma sta_conv_pi0 A A' B B' s :
  A === A' -> B === B' -> Pi0 A B s === Pi0 A' B' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Pi0 A' B s)).
  apply: (conv_hom ((Pi0^~ B)^~ s)) r1=>x y p. apply: sta_pstep_pi0...
  apply: (conv_hom ((Pi0 A')^~ s)) r2=>x y p. apply: sta_pstep_pi0...
Qed.

Lemma sta_conv_pi1 A A' B B' s :
  A === A' -> B === B' -> Pi1 A B s === Pi1 A' B' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Pi1 A' B s)).
  apply: (conv_hom ((Pi1^~ B)^~ s)) r1=>x y p. apply: sta_pstep_pi1...
  apply: (conv_hom ((Pi1 A')^~ s)) r2=>x y p. apply: sta_pstep_pi1...
Qed.

Lemma sta_conv_lam0 A A' m m' s :
  A === A' -> m === m' -> Lam0 A m s === Lam0 A' m' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Lam0 A' m s)).
  apply: (conv_hom ((Lam0^~ m)^~ s)) r1=>x y p. apply: sta_pstep_lam0...
  apply: (conv_hom ((Lam0 A')^~ s)) r2=>x y p. apply: sta_pstep_lam0...
Qed.

Lemma sta_conv_lam1 A A' m m' s :
  A === A' -> m === m' -> Lam1 A m s === Lam1 A' m' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Lam1 A' m s)).
  apply: (conv_hom ((Lam1^~ m)^~ s)) r1=>x y p. apply: sta_pstep_lam1...
  apply: (conv_hom ((Lam1 A')^~ s)) r2=>x y p. apply: sta_pstep_lam1...
Qed.

Lemma sta_conv_app0 m m' n n' :
  m === m' -> n === n' -> App0 m n === App0 m' n'.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (App0 m' n)).
  apply: (conv_hom (App0^~ n)) r1=>x y p. apply: sta_pstep_app0...
  apply: conv_hom r2=>x y p. apply: sta_pstep_app0...
Qed.

Lemma sta_conv_app1 m m' n n' :
  m === m' -> n === n' -> App1 m n === App1 m' n'.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (App1 m' n)).
  apply: (conv_hom (App1^~ n)) r1=>x y p. apply: sta_pstep_app1...
  apply: conv_hom r2=>x y p. apply: sta_pstep_app1...
Qed.

Lemma sta_conv_sig0 A A' B B' s :
  A === A' -> B === B' -> Sig0 A B s === Sig0 A' B' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Sig0 A' B s)).
  apply: (conv_hom ((Sig0^~ B)^~ s)) r1=>x y p. apply: sta_pstep_sig0...
  apply: (conv_hom ((Sig0 A')^~ s)) r2=>x y p. apply: sta_pstep_sig0...
Qed.

Lemma sta_conv_sig1 A A' B B' s :
  A === A' -> B === B' -> Sig1 A B s === Sig1 A' B' s.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Sig1 A' B s)).
  apply: (conv_hom ((Sig1^~ B)^~ s)) r1=>x y p. apply: sta_pstep_sig1...
  apply: (conv_hom ((Sig1 A')^~ s)) r2=>x y p. apply: sta_pstep_sig1...
Qed.

Lemma sta_conv_pair0 m m' n n' t :
  m === m' -> n === n' -> Pair0 m n t === Pair0 m' n' t.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Pair0 m' n t)).
  apply: (conv_hom ((Pair0^~ n)^~ t)) r1=>x y p. apply: sta_pstep_pair0...
  apply: (conv_hom ((Pair0 m')^~ t)) r2=>x y p. apply: sta_pstep_pair0...
Qed.

Lemma sta_conv_pair1 m m' n n' t :
  m === m' -> n === n' -> Pair1 m n t === Pair1 m' n' t.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Pair1 m' n t)).
  apply: (conv_hom ((Pair1^~ n)^~ t)) r1=>x y p. apply: sta_pstep_pair1...
  apply: (conv_hom ((Pair1 m')^~ t)) r2=>x y p. apply: sta_pstep_pair1...
Qed.

Lemma sta_conv_letin A A' m m' n n' :
  A === A' -> m === m' -> n === n' -> LetIn A m n === LetIn A' m' n'.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2 r3.
  apply: (conv_trans (LetIn A' m n)).
  apply: (conv_hom ((LetIn^~ m)^~ n)) r1=>x y p. apply: sta_pstep_letin...
  apply: (conv_trans (LetIn A' m' n)).
  apply: (conv_hom (LetIn A'^~ n)) r2=>x y p. apply: sta_pstep_letin...
  apply: (conv_hom (LetIn A' m')) r3=>x y p. apply: sta_pstep_letin...
Qed.

Lemma sta_conv_fix A A' m m' :
  A === A' -> m === m' -> Fix A m === Fix A' m'.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2.
  apply: (conv_trans (Fix A' m)).
  apply: (conv_hom (Fix^~ m)) r1=>x y p. apply: sta_pstep_fix...
  apply: (conv_hom (Fix A')) r2=>x y p. apply: sta_pstep_fix...
Qed.

Lemma sta_conv_ifte A A' m m' n1 n1' n2 n2' :
  A === A' -> m === m' -> n1 === n1' -> n2 === n2' ->
  Ifte A m n1 n2 === Ifte A' m' n1' n2'.
Proof with eauto using sta_pstep_refl.
  move=> r1 r2 r3 r4.
  apply: (conv_trans (Ifte A' m n1 n2)).
  apply: (conv_hom (((Ifte^~ m)^~ n1)^~ n2)) r1=>x y p. apply: sta_pstep_ifte...
  apply: (conv_trans (Ifte A' m' n1 n2)).
  apply: (conv_hom (((Ifte A')^~ n1)^~ n2)) r2=>x y p. apply: sta_pstep_ifte...
  apply: (conv_trans (Ifte A' m' n1' n2)).
  apply: (conv_hom ((Ifte A' m')^~ n2)) r3=>x y p. apply: sta_pstep_ifte...
  apply: (conv_hom (Ifte A' m' n1')) r4=>x y p. apply: sta_pstep_ifte...
Qed.

Lemma sta_conv_io A A' : A === A' -> IO A === IO A'.
Proof. move=>r. apply: (conv_hom IO) r=>x y p. exact: sta_pstep_io. Qed.

Lemma sta_conv_return m m' : m === m' -> Return m === Return m'.
Proof. move=>r. apply: (conv_hom Return) r=>x y p. exact: sta_pstep_return. Qed.

Lemma sta_conv_bind m m' n n' :
  m === m' -> n === n' -> Bind m n === Bind m' n'.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Bind m' n)).
  apply: (conv_hom (Bind^~ n)) r1=>x y p. apply: sta_pstep_bind...
  apply: (conv_hom (Bind m')) r2=>x y p. apply: sta_pstep_bind...
Qed.

Lemma sta_conv_act0 r A A' B B' :
  A === A' -> B === B' -> Act0 r A B === Act0 r A' B'.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Act0 r A' B)).
  apply: (conv_hom (Act0 r ^~ B)) r1=>x y p. apply: sta_pstep_act0...
  apply: (conv_hom (Act0 r A')) r2=>x y p. apply: sta_pstep_act0...
Qed.

Lemma sta_conv_act1 r A A' B B' :
  A === A' -> B === B' -> Act1 r A B === Act1 r A' B'.
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Act1 r A' B)).
  apply: (conv_hom (Act1 r ^~ B)) r1=>x y p. apply: sta_pstep_act1...
  apply: (conv_hom (Act1 r A')) r2=>x y p. apply: sta_pstep_act1...
Qed.

Lemma sta_conv_ch r A A' :
  A === A' -> Ch r A === Ch r A'.
Proof.
  move=>c. apply: (conv_hom (Ch r)) c=>x y. exact: sta_pstep_ch.
Qed.

Lemma sta_conv_fork A A' m m' :
  A === A' -> m === m' ->  Fork A m === Fork A' m'. 
Proof with eauto using sta_pstep_refl.
  move=>r1 r2.
  apply: (conv_trans (Fork A' m)).
  apply: (conv_hom (Fork^~ m)) r1=>x y p. apply: sta_pstep_fork...
  apply: (conv_hom (Fork A')) r2=>x y p. apply: sta_pstep_fork...
Qed.

Lemma sta_conv_recv0 m m' :
  m === m' -> Recv0 m === Recv0 m'.
Proof. move=>r. apply: (conv_hom Recv0) r=>x y. exact: sta_pstep_recv0. Qed.

Lemma sta_conv_recv1 m m' :
  m === m' -> Recv1 m === Recv1 m'.
Proof. move=>r. apply: (conv_hom Recv1) r=>x y. exact: sta_pstep_recv1. Qed.

Lemma sta_conv_send0 m m' :
  m === m' -> Send0 m === Send0 m'.
Proof. move=>r. apply: (conv_hom Send0) r=>x y. exact: sta_pstep_send0. Qed.

Lemma sta_conv_send1 m m' :
  m === m' -> Send1 m === Send1 m'.
Proof. move=>r. apply: (conv_hom Send1) r=>x y. exact: sta_pstep_send1. Qed.

Lemma sta_conv_close m m' :
  m === m' -> Close m === Close m'.
Proof. move=>r. apply: (conv_hom Close) r=>x y. exact: sta_pstep_close. Qed.

Lemma sta_conv_wait m m' :
  m === m' -> Wait m === Wait m'.
Proof. move=>r. apply: (conv_hom Wait) r=>x y. exact: sta_pstep_wait. Qed.

Lemma sta_conv_subst σ m n :
  m === n -> m.[σ] === n.[σ].
Proof.
  move=>c.
  apply: conv_hom c=>x y.
  exact: sta_pstep_subst.
Qed.

Definition sconv (σ τ : var -> term) := forall x, σ x === τ x.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: sta_conv_subst. Qed.

Lemma sconv_upn n σ τ : sconv σ τ -> sconv (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sconv_up. by asimpl.
Qed.

#[export] Hint Resolve
  sta_conv_pi0 sta_conv_pi1
  sta_conv_lam0 sta_conv_lam1
  sta_conv_app0 sta_conv_app1
  sta_conv_sig0 sta_conv_sig1
  sta_conv_pair0 sta_conv_pair1 sta_conv_letin
  sta_conv_fix sta_conv_ifte
  sta_conv_io sta_conv_return sta_conv_bind
  sta_conv_act0 sta_conv_act1 sta_conv_ch
  sta_conv_fork
  sta_conv_recv0 sta_conv_send0
  sta_conv_recv1 sta_conv_send1
  sta_conv_close sta_conv_wait
  sconv_up sconv_upn : sta_conv_congr.

Lemma sta_conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 8 with sta_conv_congr. Qed.

Lemma sta_conv_beta m n1 n2 : n1 === n2 -> m.[n1/] === m.[n2/].
Proof. move=> c. by apply: sta_conv_compat => -[]. Qed.

Definition sta_psstep (σ τ : var -> term) := forall x, (σ x) ≈> (τ x).

Lemma sta_psstep_refl σ : sta_psstep σ σ.
Proof with eauto using sta_pstep_refl. elim... Qed.

Lemma sta_psstep_up σ τ : sta_psstep σ τ -> sta_psstep (up σ) (up τ).
Proof with eauto using sta_pstep, sta_pstep_refl.
  move=> A [|n] //=. asimpl... asimpl; apply: sta_pstep_subst. exact: A.
Qed.

Lemma sta_psstep_upn n σ τ : sta_psstep σ τ -> sta_psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/sta_psstep_up. by asimpl.
Qed.

Lemma sta_pstep_compat m n σ τ :
  m ≈> n -> sta_psstep σ τ -> m.[σ] ≈> n.[τ].
Proof with eauto 8 using sta_pstep, sta_psstep_up.
  move=> ps. elim: ps σ τ=>{m n}...
  { move=> A m m' n n' s ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (sta_pstep_beta0 A.[σ] s (ih1 _ _ (sta_psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=> A m m' n n' s ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (sta_pstep_beta1 A.[σ] s (ih1 _ _ (sta_psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    pose proof
      (sta_pstep_letinE0 A.[up σ] s (ihm1 _ _ pss)
                             (ihm2 _ _ pss) (ihn _ _ (sta_psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    pose proof (sta_pstep_letinE1 A.[up σ] s (ihm1 _ _ pss)
                                  (ihm2 _ _ pss) (ihn _ _ (sta_psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A A' m m' pA ihA pm ihm σ τ pss. asimpl.
    pose proof (sta_pstep_fixE (ihA _ _ pss) (ihm _ _ (sta_psstep_up pss))).
    by asimpl in H. }
  { move=>m m' n n' ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (sta_pstep_bindE (ih1 _ _ pss)) (ih2 _ _ (sta_psstep_up pss)) as H.
    by asimpl in H. }
Qed.

Lemma sta_psstep_compat s1 s2 σ τ:
  sta_psstep σ τ -> s1 ≈> s2 -> sta_psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma sta_pstep_subst_term m n n' :
  n ≈> n' -> m.[n/] ≈> m.[n'/].
Proof with eauto using sta_pstep_compat, sta_psstep_refl, sta_psstep_compat.
  move...
Qed.

Lemma sta_pstep_compat_beta m m' n n' :
  m ≈> m' -> n ≈> n' -> m.[n/] ≈> m'.[n'/].
Proof with eauto using sta_pstep_compat, sta_psstep_refl, sta_psstep_compat.
  move...
Qed.

Lemma sta_pstep_diamond m m1 m2 :
  m ≈> m1 -> m ≈> m2 -> exists2 m', m1 ≈> m' & m2 ≈> m'.
Proof with eauto 8 using
  sta_pstep, sta_pstep_refl,
  sta_pstep_compat, sta_pstep_compat_beta,
  sta_psstep_compat, sta_psstep_refl.
  move=>ps. elim: ps m2=>{m m1}...
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[B0 pB1 pB2]:=ihB _ H4.
    exists (Pi0 A0 B0 s)... }
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[B0 pB1 pB2]:=ihB _ H4.
    exists (Pi1 A0 B0 s)... }
  { move=>A A' m m' s pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[m0 pm1 pm2]:=ihm _ H4.
    exists (Lam0 A0 m0 s)... }
  { move=>A A' m m' s pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[m0 pm1 pm2]:=ihm _ H4.
    exists (Lam1 A0 m0 s)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (App0 m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:(Lam0 A m0 s) ≈> (Lam0 A m'0 s)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (App1 m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:(Lam1 A m0 s) ≈> (Lam1 A m'0 s)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>A m m' n n' s pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H6.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H4.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists (m0.[n0/])... } }
  { move=>A m m' n n' s pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H6.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H4.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists (m0.[n0/])... } }
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[B0 pB1 pB2]:=ihB _ H4.
    exists (Sig0 A0 B0 s)... }
  { move=>A A' B B' s pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H3.
    have[B0 pB1 pB2]:=ihB _ H4.
    exists (Sig1 A0 B0 s)... }
  { move=>m m' n n' s pm ihm pn ihn m2 p. inv p.
    have[m0 pm1 pm2]:=ihm _ H3.
    have[n0 pn1 pn2]:=ihn _ H4.
    exists (Pair0 m0 n0 s)... }
  { move=>m m' n n' s pm ihm pn ihn m2 p. inv p.
    have[m0 pm1 pm2]:=ihm _ H3.
    have[n0 pn1 pn2]:=ihn _ H4.
    exists (Pair1 m0 n0 s)... }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn m2 p. inv p.
    { have[A0 pA1 pA2]:=ihA _ H2.
      have[m0 pm1 pm2]:=ihm _ H4.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists (LetIn A0 m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:(Pair0 m1 m0 s) ≈> (Pair0 m1' m2' s)...
      have[n0 pn1 pn2]:=ihn _ H5.
      inv pm1. inv pm2.
      exists n0.[n'2,m'/]... }
    { inv pm.
      have/ihm[mx pm1 pm2]:(Pair1 m1 m0 s) ≈> (Pair1 m1' m2' s)...
      have[n0 pn1 pn2]:=ihn _ H5.
      inv pm1. inv pm2.
      exists n0.[n'2,m'/]... } }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn m0 p. inv p.
    { inv H4.
      have[m1x pm11 pm12]:=ihm1 _ H6.
      have[m2x pm21 pm22]:=ihm2 _ H7.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists n0.[m2x,m1x/]... }
    { have[m1x pm11 pm12]:=ihm1 _ H5.
      have[m2x pm21 pm22]:=ihm2 _ H6.
      have[n0 pn1 pn2]:=ihn _ H7.
      exists n0.[m2x,m1x/]... } }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn m0 p. inv p.
    { inv H4.
      have[m1x pm11 pm12]:=ihm1 _ H6.
      have[m2x pm21 pm22]:=ihm2 _ H7.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists n0.[m2x,m1x/]... }
    { have[m1x pm11 pm12]:=ihm1 _ H5.
      have[m2x pm21 pm22]:=ihm2 _ H6.
      have[n0 pn1 pn2]:=ihn _ H7.
      exists n0.[m2x,m1x/]... } }
  { move=>A A' m m' pA ihA pm ihm m0 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (Fix Ax mx)... }
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... } }
  { move=>A A' m m' pA ihA pm ihm m0 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... }
    { have[Ax pA1 pA2]:=ihA _ H1.
      have[mx pm1 pm2]:=ihm _ H3.
      exists (mx.[Fix Ax mx/])... } }
  { move=>A A' m m' n1 n1' n2 n2' pA ihA pm ihm pn1 ihn1 pn2 ihn2 m0 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H3.
      have[mx pm1 pm2]:=ihm _ H5.
      have[n1x pn11 pn12]:=ihn1 _ H6.
      have[n2x pn21 pn22]:=ihn2 _ H7.
      exists (Ifte Ax mx n1x n2x)... }
    { inv pm.
      have[nx pn11 pn12]:=ihn1 _ H4.
      exists nx... }
    { inv pm.
      have[nx pn21 pn22]:=ihn2 _ H4.
      exists nx... } }
  { move=>A n1 n1' n2 pn ih m0 p. inv p.
    { inv H5.
      have[nx pn1 pn2]:=ih _ H6.
      exists nx... }
    { have[nx pn1 pn2]:=ih _ H3.
      exists nx... } }
  { move=>A n1 n1' n2 pn ih m0 p. inv p.
    { inv H5.
      have[nx pn1 pn2]:=ih _ H7.
      exists nx... }
    { have[nx pn1 pn2]:=ih _ H3.
      exists nx... } }
  { move=>A A' pA ihA m0 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H0.
    exists (IO A0)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[m0 pm1 pm2]:=ihm _ H0.
    exists (Return m0)... }
  { move=>m m' n n' pm ihm pn ihn m0 p. inv p.
    { have[mx pm1 pm2]:=ihm _ H1.
      have[nx pn1 pn2]:=ihn _ H3.
      exists (Bind mx nx)... }
    { have[mx pm1 pm2]:=ihm _ (sta_pstep_return H1).
      inv pm. inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists n0.[m'/]... } }
  { move=>m m' n n' pm ihm pn ihn m0 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H0.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists n0.[m0/]... }
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists n0.[m0/]... } }
  { move=>r A A' B B' pA ihA pB ihB m0 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[Bx pB1 pB2]:=ihB _ H4.
    exists (Act0 r Ax Bx)... }
  { move=>r A A' B B' pA ihA pB ihB m0 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H3.
    have[Bx pB1 pB2]:=ihB _ H4.
    exists (Act1 r Ax Bx)... }
  { move=>r A A' pA ihA m0 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H2.
    exists (Ch r Ax)... }
  { move=>x y m2 p. inv p. exists (CVar x)... }
  { move=>A A' m m' pA ihA pm ihm m0 p. inv p.
    have[Ax pA1 pA2]:=ihA _ H1.
    have[mx pm1 pm2]:=ihm _ H3.
    exists (Fork Ax mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Recv0 mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Recv1 mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Send0 mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Send1 mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Close mx)... }
  { move=>m m' pm ihm m0 p. inv p.
    have[mx pm1 pm2]:=ihm _ H0.
    exists (Wait mx)... }
Qed.

Lemma strip m m1 m2 :
  m ≈> m1 -> m ≈>* m2 -> exists2 m', m1 ≈>* m' & m2 ≈> m'.
Proof with eauto using sta_pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(sta_pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
Qed.

Theorem confluence :
  confluent sta_pstep.
Proof with eauto using sta_pstep, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
Qed.

Theorem church_rosser :
  CR sta_pstep.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma sta_pred_var_inv x y : Var x ≈>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  by inv r2.
Qed.

Lemma sta_pred_sort_inv s A : Sort s ≈>* A -> A = Sort s.
Proof.
  elim=>//y z r1 e r2; subst.
  by inv r2.
Qed.

Lemma sta_pred_pi0_inv A B s x :
  Pi0 A B s ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Pi0 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_pi1_inv A B s x :
  Pi1 A B s ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Pi1 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd [A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_lam0_inv A m x s :
  Lam0 A m s ≈>* x ->
  exists A' m',
    A ≈>* A' /\ m ≈>* m' /\ x = Lam0 A' m' s.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'0. eauto using star.
Qed.

Lemma sta_pred_lam1_inv A m x s :
  Lam1 A m s ≈>* x ->
  exists A' m',
    A ≈>* A' /\ m ≈>* m' /\ x = Lam1 A' m' s.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1 [A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'0. eauto using star.
Qed.

Lemma sta_pred_sig0_inv A B s x :
  Sig0 A B s ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Sig0 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_sig1_inv A B s x :
  Sig1 A B s ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Sig1 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_pair0_inv m n s x :
  Pair0 m n s ≈>* x ->
  exists m' n',
    m ≈>* m' /\ n ≈>* n' /\ x = Pair0 m' n' s.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_pair1_inv m n s x :
  Pair1 m n s ≈>* x ->
  exists m' n',
    m ≈>* m' /\ n ≈>* n' /\ x = Pair1 m' n' s.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_unit_inv x : Unit ≈>* x -> x = Unit.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_ii_inv x : II ≈>* x -> x = II.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_bool_inv x : Bool ≈>* x -> x = Bool.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_tt_inv x : TT ≈>* x -> x = TT.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_ff_inv x : FF ≈>* x -> x = FF.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_io_inv A x :
  IO A ≈>* x ->
  exists A',
    A ≈>* A' /\ x = IO A'.
Proof.
  elim.
  by exists A.
  move=>y z rd1[A'[rd2 e]]st. subst. inv st.
  exists A'0. eauto using star.
Qed.

Lemma sta_pred_return_inv m x :
  Return m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Return m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_proto_inv x : Proto ≈>* x -> x = Proto.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_stop_inv x : Stop ≈>* x -> x = Stop.
Proof.
  elim=>//.
  move=>y z rd e st. subst. by inv st.
Qed.

Lemma sta_pred_act0_inv r A B x :
  Act0 r A B ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Act0 r A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_act1_inv r A B x :
  Act1 r A B ≈>* x ->
  exists A' B',
    A ≈>* A' /\ B ≈>* B' /\ x = Act1 r A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_pred_ch_inv r A x :
  Ch r A ≈>* x ->
  exists A',
    A ≈>* A' /\ x = Ch r A'.
Proof.
  elim.
  by exists A.
  move=>y z rd1[A'[rd2 e]]st. subst. inv st.
  exists A'0. eauto using star.
Qed.

Lemma sta_pred_cvar_inv x y :
  CVar x ≈>* y -> exists x, y = CVar x.
Proof.
  elim=>//. by exists x.
  move=>y0 z rd[x0 e]st. subst. inv st. by exists y0.
Qed.

Lemma sta_pred_fork_inv A m x :
  Fork A m ≈>* x ->
  exists A' m',
    A ≈>* A' /\ m ≈>* m' /\ x = Fork A' m'.
Proof.
  elim.
  exists A. by exists m.
  move=>y z rd[A'[m'[rdA[rdm e]]]]st. subst. inv st.
  exists A'0. exists m'0. eauto using star.
Qed.

Lemma sta_pred_recv0_inv m x :
  Recv0 m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Recv0 m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_recv1_inv m x :
  Recv1 m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Recv1 m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_send0_inv m x :
  Send0 m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Send0 m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_send1_inv m x :
  Send1 m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Send1 m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_close_inv m x :
  Close m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Close m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sta_pred_wait_inv m x :
  Wait m ≈>* x ->
  exists m',
    m ≈>* m' /\ x = Wait m'.
Proof.
  elim.
  by exists m.
  move=>y z rd1[m'[rd2 e]]st. subst. inv st.
  exists m'0. eauto using star.
Qed.

Lemma sort_inj s1 s2 :
  Sort s1 === Sort s2 -> s1 = s2.
Proof.
  move/church_rosser=>[x/sta_pred_sort_inv->/sta_pred_sort_inv[->]]//.
Qed.

Lemma pi0_inj A A' B B' s s' :
  Pi0 A B s === Pi0 A' B' s' ->
    A === A' /\ B === B' /\ s = s'.
Proof.
  move/church_rosser=>
    [x/sta_pred_pi0_inv[A1[B1[rA1[rB1->]]]]
      /sta_pred_pi0_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma pi1_inj A A' B B' s s' :
  Pi1 A B s === Pi1 A' B' s' ->
    A === A' /\ B === B' /\ s = s'.
Proof.
  move/church_rosser=>
    [x/sta_pred_pi1_inv[A1[B1[rA1[rB1->]]]]
      /sta_pred_pi1_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma sig0_inj A A' B B' s s' :
  Sig0 A B s === Sig0 A' B' s' ->
    A === A' /\ B === B' /\ s = s'.
Proof.
  move/church_rosser=>
    [x/sta_pred_sig0_inv[A1[B1[rA1[rB1->]]]]
      /sta_pred_sig0_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma sig1_inj A A' B B' s s' :
  Sig1 A B s === Sig1 A' B' s' ->
    A === A' /\ B === B' /\ s = s'.
Proof.
  move/church_rosser=>
    [x/sta_pred_sig1_inv[A1[B1[rA1[rB1->]]]]
      /sta_pred_sig1_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma io_inj A A' : IO A === IO A' -> A === A'.
Proof.
  move/church_rosser=>
    [x/sta_pred_io_inv[A1[r1->]]/sta_pred_io_inv[A2[r2[e]]]]; subst.
  apply: join_conv.
  apply: r1.
  apply: r2.
Qed.

Lemma act0_inj r r' A A' B B' :
  Act0 r A B === Act0 r' A' B' ->
  A === A' /\ B === B' /\ r = r'.
Proof.
  move/church_rosser=>[x/sta_pred_act0_inv r1/sta_pred_act0_inv r2].
  move:r1=>[A1[B1[rA1[rB1 e1]]]].
  move:r2=>[A2[B2[rA2[rB2 e2]]]].
  subst. inv e2. eauto using join_conv.
Qed.

Lemma act1_inj r r' A A' B B' :
  Act1 r A B === Act1 r' A' B' ->
  A === A' /\ B === B' /\ r = r'.
Proof.
  move/church_rosser=>[x/sta_pred_act1_inv r1/sta_pred_act1_inv r2].
  move:r1=>[A1[B1[rA1[rB1 e1]]]].
  move:r2=>[A2[B2[rA2[rB2 e2]]]].
  subst. inv e2. eauto using join_conv.
Qed.

Lemma ch_inj r r' A A' :
  Ch r A === Ch r' A' -> r = r' /\ A === A'.
Proof.
  move/church_rosser=>[x/sta_pred_ch_inv r1/sta_pred_ch_inv r2].
  move:r1=>[A1[rA1 e1]].
  move:r2=>[A2[rA2 e2]].
  subst. inv e2. eauto using join_conv.
Qed.

Ltac pred_inv m H :=
  match m with
  | Var    => apply sta_pred_var_inv in H
  | Sort   => apply sta_pred_sort_inv in H
  | Pi0    => apply sta_pred_pi0_inv in H
  | Pi1    => apply sta_pred_pi1_inv in H
  | Lam0   => apply sta_pred_lam0_inv in H
  | Lam1   => apply sta_pred_lam1_inv in H
  | Sig0   => apply sta_pred_sig0_inv in H
  | Sig1   => apply sta_pred_sig1_inv in H
  | Pair0  => apply sta_pred_pair0_inv in H
  | Pair1  => apply sta_pred_pair1_inv in H
  | Unit   => apply sta_pred_unit_inv in H
  | II     => apply sta_pred_ii_inv in H
  | Bool   => apply sta_pred_bool_inv in H
  | TT     => apply sta_pred_tt_inv in H
  | FF     => apply sta_pred_ff_inv in H
  | IO     => apply sta_pred_io_inv in H
  | Return => apply sta_pred_return_inv in H
  | Proto  => apply sta_pred_proto_inv in H
  | Stop   => apply sta_pred_stop_inv in H
  | Act0   => apply sta_pred_act0_inv in H
  | Act1   => apply sta_pred_act1_inv in H
  | Ch     => apply sta_pred_ch_inv in H
  | CVar   => apply sta_pred_cvar_inv in H
  | Fork   => apply sta_pred_fork_inv in H
  | Recv0  => apply sta_pred_recv0_inv in H
  | Recv1  => apply sta_pred_recv1_inv in H
  | Send0  => apply sta_pred_send0_inv in H
  | Send1  => apply sta_pred_send1_inv in H
  | Close  => apply sta_pred_close_inv in H
  | Wait   => apply sta_pred_wait_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : sta_pred (?m _) _ |- _ ]         => pred_inv m H
  | [ H : sta_pred (?m _ _) _ |- _ ]       => pred_inv m H
  | [ H : sta_pred (?m _ _ _) _ |- _ ]     => pred_inv m H
  | [ H : sta_pred (?m _ _ _ _) _ |- _ ]   => pred_inv m H
  | [ H : sta_pred (?m _ _ _ _ _) _ |- _ ] => pred_inv m H
  | [ H : sta_pred ?m _ |- _ ]             => pred_inv m H
  end;
  firstorder; subst;
  match goal with
  | [ H : _ = _ |- _ ] => inv H
  end.

Ltac solve_conv :=
  match goal with
  | [ H : ?t1 === ?t2 |- _ ] =>
    assert (~ t1 === t2) by solve_conv'
  end; eauto.
