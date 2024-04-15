From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_sort s l :
  pstep (Sort s l) (Sort s l)
| pstep_pi0 A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi0 A B s) (Pi0 A' B' s)
| pstep_pi1 A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi1 A B s) (Pi1 A' B' s)
| pstep_lam0 A A' m m' s :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam0 A m s) (Lam0 A' m' s)
| pstep_lam1 A A' m m' s :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam1 A m s) (Lam1 A' m' s)
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta0 A m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam0 A m s) n) (m'.[n'/])
| pstep_beta1 A m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam1 A m s) n) (m'.[n'/])
| pstep_sig0 A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (Sig0 A B s) (Sig0 A' B' s)
| pstep_sig1 A A' B B' s :
  pstep A A' ->
  pstep B B' ->
  pstep (Sig1 A B s) (Sig1 A' B' s)
| pstep_pair0 m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (Pair0 m n s) (Pair0 m' n' s)
| pstep_pair1 m m' n n' s :
  pstep m m' ->
  pstep n n' ->
  pstep (Pair1 m n s) (Pair1 m' n' s)
| pstep_letin A A' m m' n n' :
  pstep A A' ->
  pstep m m' ->
  pstep n n' ->
  pstep (LetIn A m n) (LetIn A' m' n')
| pstep_iota0 A m1 m1' m2 m2' n n' s :
  pstep m1 m1' ->
  pstep m2 m2' ->
  pstep n n' ->
  pstep (LetIn A (Pair0 m1 m2 s) n) (n'.[m2',m1'/])
| pstep_iota1 A m1 m1' m2 m2' n n' s :
  pstep m1 m1' ->
  pstep m2 m2' ->
  pstep n n' ->
  pstep (LetIn A (Pair1 m1 m2 s) n) (n'.[m2',m1'/])
| pstep_bool :
  pstep Bool Bool
| pstep_tt :
  pstep TT TT
| pstep_ff :
  pstep FF FF
| pstep_ifte A A' m m' n1 n1' n2 n2' :
  pstep A A' ->
  pstep m m' ->
  pstep n1 n1' ->
  pstep n2 n2' ->
  pstep (Ifte A m n1 n2) (Ifte A' m' n1' n2')
| pstep_ifteTT A n1 n1' n2 :
  pstep n1 n1' ->
  pstep (Ifte A TT n1 n2) n1'
| pstep_ifteFF A n1 n2 n2' :
  pstep n2 n2' ->
  pstep (Ifte A FF n1 n2) n2'
| pstep_id A A' m m' n n' :
  pstep A A' ->
  pstep m m' ->
  pstep n n' ->
  pstep (Id A m n) (Id A' m' n')
| pstep_refl m m' :
  pstep m m' ->
  pstep (Refl m) (Refl m')
| pstep_rw A A' H H' P P' :
  pstep A A' ->
  pstep H H' ->
  pstep P P' ->
  pstep (Rw A H P) (Rw A' H' P')
| pstep_rwE A H H' m :
  pstep H H' ->
  pstep (Rw A H (Refl m)) H'
| pstep_box : pstep Box Box
| pstep_ptr l : pstep (Ptr l) (Ptr l).

Definition sred σ τ := forall x : var, (σ x) ~>* (τ x).

Lemma sta_step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using sta_step.
  { move=> A m n s σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_beta0. autosubst. }
  { move=> A m n s σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply sta_step_beta1. autosubst. }
  { move=>A m1 m2 n s σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/]).
    apply: sta_step_iota0. autosubst. }
  { move=>A m1 m2 n s σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/]).
    apply: sta_step_iota1. autosubst. }
Qed.

Lemma sta_red_app m m' n n' :
  m ~>* m' -> n ~>* n' -> App m n ~>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: sta_step_appL.
  apply: star_hom r2. exact: sta_step_appR.
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

Lemma sta_red_ifte A A' m m' n1 n1' n2 n2' :
  A ~>* A' -> m ~>* m' -> n1 ~>* n1' -> n2 ~>* n2' -> Ifte A m n1 n2 ~>* Ifte A' m' n1' n2'.
Proof.
  move=>rA rm rn1 rn2.
  apply: (star_trans (Ifte A' m n1 n2)).
  apply: (star_hom (((Ifte^~ m)^~ n1)^~ n2)) rA=>x y. exact: sta_step_ifteA.
  apply: (star_trans (Ifte A' m' n1 n2)).
  apply: (star_hom (((Ifte A')^~ n1)^~ n2)) rm=>x y. exact: sta_step_ifteM.
  apply: (star_trans (Ifte A' m' n1' n2)).
  apply: (star_hom ((Ifte A' m')^~ n2)) rn1=>x y. exact: sta_step_ifteN1.
  apply: (star_hom (Ifte A' m' n1')) rn2=>x y. exact: sta_step_ifteN2.
Qed.

Lemma sta_red_id A A' m m' n n' :
  A ~>* A' -> m ~>* m' -> n ~>* n' -> Id A m n ~>* Id A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Id A' m n)).
  apply: (star_hom ((Id^~ m)^~ n)) r1=>x y. exact: sta_step_idA.
  apply: (star_trans (Id A' m' n)).
  apply: (star_hom (Id A'^~ n)) r2=>x y. exact: sta_step_idL.
  apply: (star_hom (Id A' m')) r3=>x y. exact: sta_step_idR.
Qed.

Lemma sta_red_refl m m' :
  m ~>* m' -> Refl m ~>* Refl m'.
Proof.
  move=>r.
  apply: (star_hom Refl) r=>x y. exact: sta_step_refl.
Qed.

Lemma sta_red_rw A A' H H' P P' :
  A ~>* A' -> H ~>* H' -> P ~>* P' -> Rw A H P ~>* Rw A' H' P'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Rw A' H P)).
  apply: (star_hom ((Rw^~ H)^~ P)) r1=>x y. exact: sta_step_rwA.
  apply: (star_trans (Rw A' H' P)).
  apply: (star_hom (Rw A'^~P)) r2=>x y. exact: sta_step_rwH.
  apply: (star_hom (Rw A' H')) r3=>x y. exact: sta_step_rwP.
Qed.

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

#[global] Hint Resolve
  sta_red_app
  sta_red_lam0 sta_red_lam1
  sta_red_pi0 sta_red_pi1
  sta_red_sig0 sta_red_sig1
  sta_red_pair0 sta_red_pair1
  sta_red_letin sta_red_ifte
  sta_red_id sta_red_refl sta_red_rw
  sred_up sred_upn : sta_red_congr.

Lemma sta_red_compat σ τ s : sred σ τ -> sta_red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with sta_red_congr. Qed.

Definition sconv (σ τ : var -> term) := forall x, σ x === τ x.

Lemma sta_conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (App m' n)).
  apply: (conv_hom (App^~ n)) r1=>x y. exact: sta_step_appL.
  apply: conv_hom r2. exact: sta_step_appR.
Qed.

Lemma sta_conv_lam0 A A' m m' s :
  A === A' -> m === m' -> Lam0 A m s === Lam0 A' m' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam0 A' m s)).
  apply: (conv_hom ((Lam0^~ m)^~ s)) r1=>x y. exact: sta_step_lam0L.
  apply: (conv_hom ((Lam0 A')^~ s)) r2=>x y. exact: sta_step_lam0R.
Qed.

Lemma sta_conv_lam1 A A' m m' s :
  A === A' -> m === m' -> Lam1 A m s === Lam1 A' m' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam1 A' m s)).
  apply: (conv_hom ((Lam1^~ m)^~ s)) r1=>x y. exact: sta_step_lam1L.
  apply: (conv_hom ((Lam1 A')^~ s)) r2=>x y. exact: sta_step_lam1R.
Qed.

Lemma sta_conv_pi0 A A' B B' s :
  A === A' -> B === B' -> Pi0 A B s === Pi0 A' B' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi0 A' B s)).
  apply: (conv_hom ((Pi0^~ B)^~ s)) r1=>x y. exact: sta_step_pi0L.
  apply: (conv_hom ((Pi0 A')^~ s)) r2=>x y. exact: sta_step_pi0R.
Qed.

Lemma sta_conv_pi1 A A' B B' s :
  A === A' -> B === B' -> Pi1 A B s === Pi1 A' B' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi1 A' B s)).
  apply: (conv_hom ((Pi1^~ B)^~ s)) r1=>x y. exact: sta_step_pi1L.
  apply: (conv_hom ((Pi1 A')^~ s)) r2=>x y. exact: sta_step_pi1R.
Qed.

Lemma sta_conv_sig0 A A' B B' s :
  A === A' -> B === B' -> Sig0 A B s === Sig0 A' B' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Sig0 A' B s)).
  apply: (conv_hom ((Sig0^~ B)^~ s)) r1=>x y. exact: sta_step_sig0L.
  apply: (conv_hom ((Sig0 A')^~ s)) r2=>x y. exact: sta_step_sig0R.
Qed.

Lemma sta_conv_sig1 A A' B B' s :
  A === A' -> B === B' -> Sig1 A B s === Sig1 A' B' s.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Sig1 A' B s)).
  apply: (conv_hom ((Sig1^~ B)^~ s)) r1=>x y. exact: sta_step_sig1L.
  apply: (conv_hom ((Sig1 A')^~ s)) r2=>x y. exact: sta_step_sig1R.
Qed.

Lemma sta_conv_pair0 m m' n n' t :
  m === m' -> n === n' -> Pair0 m n t === Pair0 m' n' t.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Pair0 m' n t)).
  apply: (conv_hom ((Pair0^~ n)^~ t)) r1=>x y. exact: sta_step_pair0L.
  apply: (conv_hom ((Pair0 m')^~ t)) r2=>x y. exact: sta_step_pair0R.
Qed.

Lemma sta_conv_pair1 m m' n n' t :
  m === m' -> n === n' -> Pair1 m n t === Pair1 m' n' t.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Pair1 m' n t)).
  apply: (conv_hom ((Pair1^~ n)^~ t)) r1=>x y. exact: sta_step_pair1L.
  apply: (conv_hom ((Pair1 m')^~ t)) r2=>x y. exact: sta_step_pair1R.
Qed.

Lemma sta_conv_letin A A' m m' n n' :
  A === A' -> m === m' -> n === n' -> LetIn A m n === LetIn A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (LetIn A' m n)).
  apply: (conv_hom ((LetIn^~ m)^~ n)) r1=>x y. exact: sta_step_letinA.
  apply: (conv_trans (LetIn A' m' n)).
  apply: (conv_hom (LetIn A'^~ n)) r2=>x y. exact: sta_step_letinL.
  apply: (conv_hom (LetIn A' m')) r3=>x y. exact: sta_step_letinR.
Qed.

Lemma sta_conv_ifte A A' m m' n1 n1' n2 n2' :
  A === A' -> m === m' -> n1 === n1' -> n2 === n2' -> Ifte A m n1 n2 === Ifte A' m' n1' n2'.
Proof.
  move=>rA rm rn1 rn2.
  apply: (conv_trans (Ifte A' m n1 n2)).
  apply: (conv_hom (((Ifte^~ m)^~ n1)^~ n2)) rA=>x y. exact: sta_step_ifteA.
  apply: (conv_trans (Ifte A' m' n1 n2)).
  apply: (conv_hom (((Ifte A')^~ n1)^~ n2)) rm=>x y. exact: sta_step_ifteM.
  apply: (conv_trans (Ifte A' m' n1' n2)).
  apply: (conv_hom ((Ifte A' m')^~ n2)) rn1=>x y. exact: sta_step_ifteN1.
  apply: (conv_hom (Ifte A' m' n1')) rn2=>x y. exact: sta_step_ifteN2.
Qed.

Lemma sta_conv_id A A' m m' n n' :
  A === A' -> m === m' -> n === n' -> Id A m n === Id A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Id A' m n)).
  apply: (conv_hom ((Id^~ m)^~ n)) r1=>x y. exact: sta_step_idA.
  apply: (conv_trans (Id A' m' n)).
  apply: (conv_hom (Id A'^~ n)) r2=>x y. exact: sta_step_idL.
  apply: (conv_hom (Id A' m')) r3=>x y. exact: sta_step_idR.
Qed.

Lemma sta_conv_refl m m' :
  m === m' -> Refl m === Refl m'.
Proof.
  move=>r.
  apply: (conv_hom Refl) r=>x y. exact: sta_step_refl.
Qed.

Lemma sta_conv_rw A A' H H' P P' :
  A === A' -> H === H' -> P === P' -> Rw A H P === Rw A' H' P'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Rw A' H P)).
  apply: (conv_hom ((Rw^~ H)^~ P)) r1=>x y. exact: sta_step_rwA.
  apply: (conv_trans (Rw A' H' P)).
  apply: (conv_hom (Rw A'^~ P)) r2=>x y. exact: sta_step_rwH.
  apply: (conv_hom (Rw A' H')) r3=>x y. exact: sta_step_rwP.
Qed.

Lemma sta_conv_subst σ m n :
  m === n -> m.[σ] === n.[σ].
Proof.
  move=>c.
  apply: conv_hom c.
  exact: sta_step_subst.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: sta_conv_subst. Qed.

Lemma sconv_upn n σ τ : sconv σ τ -> sconv (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sconv_up. by asimpl.
Qed.

#[export] Hint Resolve
  sta_conv_app
  sta_conv_lam0 sta_conv_lam1
  sta_conv_pi0 sta_conv_pi1
  sta_conv_sig0 sta_conv_sig1
  sta_conv_pair0 sta_conv_pair1
  sta_conv_letin sta_conv_ifte
  sta_conv_id sta_conv_refl sta_conv_rw
  sconv_up sconv_upn : sta_conv_congr.

Lemma sta_conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with sta_conv_congr. Qed.

Lemma sta_conv_beta m n1 n2 : n1 === n2 -> m.[n1/] === m.[n2/].
Proof. move=> c. by apply: sta_conv_compat => -[]. Qed.

Lemma pstep_reflexive m : pstep m m.
Proof. elim: m; eauto using pstep. Qed.
#[global] Hint Resolve pstep_reflexive.

Lemma sta_step_pstep m m' : sta_step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_reflexive. elim... Qed.

Lemma pstep_sta_red m n : pstep m n -> m ~>* n.
Proof with eauto.
  elim=>{m n}//=; eauto with sta_red_congr.
  { move=> A m m' n n' s p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|]. }
  { move=> A m m' n n' s p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|]. }
  { move=> A m1 m1' m2 m2' n n' s p1 r1 p2 r2 p r.
    apply: starES. by constructor.
    apply: (star_trans (n'.[m2,m1/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|-[]]. }
  { move=> A m1 m1' m2 m2' n n' s p1 r1 p2 r2 p r.
    apply: starES. by constructor.
    apply: (star_trans (n'.[m2,m1/])). exact: sta_red_subst.
    by apply: sta_red_compat=>-[|-[]]. }
  { move=>m m' n s p r.
    apply: starES. by constructor. eauto. }
  { move=>m m' n s p r.
    apply: starES. by constructor. eauto. }
  { move=>A H H' m p r.
    apply: starES. by constructor. eauto. }
Qed.

Lemma pstep_subst m n σ : pstep m n -> pstep m.[σ] n.[σ].
Proof with eauto using pstep, pstep_reflexive.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' s ps1 ih1 ps2 ih2 σ.
    asimpl.
    pose proof (pstep_beta0 A.[σ] s (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m m' n n' s ps1 ih1 ps2 ih2 σ.
    asimpl.
    pose proof (pstep_beta1 A.[σ] s (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ.
    asimpl.
    pose proof (pstep_iota0 A.[up σ] s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ.
    asimpl.
    pose proof (pstep_iota1 A.[up σ] s (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))).
    by asimpl in H. }
Qed.

Definition psstep (σ τ : var -> term) := forall x, pstep (σ x) (τ x).

Lemma psstep_reflexive σ : psstep σ σ.
Proof with eauto using pstep_reflexive. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_reflexive.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/psstep_up. by asimpl.
Qed.

Lemma pstep_compat m n σ τ :
  pstep m n -> psstep σ τ -> pstep m.[σ] n.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{m n}...
  { move=> A m m' n n' s ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (pstep_beta0 A.[σ] s (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=> A m m' n n' s ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (pstep_beta1 A.[σ] s (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn σ τ pss. asimpl.
    pose proof (pstep_letin (ihA _ _ (psstep_up pss)) (ihm _ _ pss) (ihn _ _ (psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    pose proof (pstep_iota0 A.[up σ] s (ihm1 _ _ pss) (ihm2 _ _ pss) (ihn _ _ (psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' s pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    pose proof (pstep_iota1 A.[up σ] s (ihm1 _ _ pss) (ihm2 _ _ pss) (ihn _ _ (psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A A' m m' n1 n1' n2 n2' pA ihA pm ihm pn1 ihn1 pn2 ihn2 σ τ pss. asimpl.
    constructor... }
  { move=>A A' H H' P P' pA ihA pH ihH pP ihP σ τ pss. asimpl.
    pose proof (pstep_rw (ihA _ _ (psstep_upn 2 pss)) (ihH _ _ pss) (ihP _ _ pss)).
    by asimpl in H0. }
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto 6 using
  pstep, pstep_refl,
  pstep_compat, pstep_compat_beta,
  psstep_compat, psstep_reflexive.
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
      exists (App m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam0 A m0 s) (Lam0 A m'0 s)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam1 A m0 s) (Lam1 A m'0 s)...
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
      have/ihm[mx pm1 pm2]:pstep (Pair0 m1 m0 s) (Pair0 m1' m2' s)...
      have[n0 pn1 pn2]:=ihn _ H5.
      inv pm1. inv pm2.
      exists n0.[n'2,m'/]... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Pair1 m1 m0 s) (Pair1 m1' m2' s)...
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
  { move=>A A' m m' n1 n1' n2 n2' pA ihA pm ihm pn1 ihn1 pn2 ihn2 m2 p. inv p.
    { have[Ax pA1 pA2]:=ihA _ H3.
      have[mx pm1 pm2]:=ihm _ H5.
      have[n1x pn11 pn12]:=ihn1 _ H6.
      have[n2x pn21 pn22]:=ihn2 _ H7.
      exists (Ifte Ax mx n1x n2x)... }
    { inv pm.
      have[n1x pn11 pn12]:=ihn1 _ H4.
      exists n1x... }
    { inv pm.
      have[n2x pn21 pn22]:=ihn2 _ H4.
      exists n2x... } }
  { move=>A n1 n1' n2 pn1 ihn1 m2 p. inv p.
    { inv H5.
      have[n1x pn11]:=ihn1 _ H6.
      exists n1x... }
    { have[n1x pn11]:=ihn1 _ H3.
      exists n1x... } }
  { move=>A n1 n2 n2' pn2 ihn2 m2 p. inv p.
    { inv H5.
      have[n2x pn21]:=ihn2 _ H7.
      exists n2x... }
    { have[n2x pn21]:=ihn2 _ H3.
      exists n2x... } }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H2.
    have[m0 pm1 pm2]:=ihm _ H4.
    have[n0 pn1 pn2]:=ihn _ H5.
    exists (Id A0 m0 n0)... }
  { move=>m m' pm ihm m2 p. inv p.
    have[m0 p1 p2]:=ihm _ H0.
    exists (Refl m0)... }
  { move=>A A' H H' P P' pA ihA pH ihH pP ihP m2 p. inv p.
    { have[A0 pA1 pA2]:=ihA _ H4.
      have[H0 pH1 pH2]:=ihH _ H6.
      have[P0 pP1 pP2]:=ihP _ H7.
      exists (Rw A0 H0 P0)... }
    { inv pP.
      have[H0 pH1 pH2]:=ihH _ H5.
      have/ihP[x p1 p2]:pstep (Refl m) (Refl m')... } }
  { move=>A H H' m pH ihH x p. inv p.
    { inv H7.
      have[H0 pH1 pH2]:=ihH _ H6.
      exists H0... }
    { have[H0 pH1 pH2]:=ihH _ H5.
      exists H0... } }
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih /sta_step_pstep p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
  apply: star_trans.
  apply: r2.
  by apply: pstep_sta_red.
Qed.

Theorem confluence :
  confluent sta_step.
Proof with eauto using sta_step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih /sta_step_pstep p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
  apply: star_trans.
  apply r3.
  apply: pstep_sta_red...
Qed.

Theorem church_rosser :
  CR sta_step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma sta_red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_sort_inv s l A :
  Sort s l ~>* A -> A = Sort s l.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma sta_red_pi0_inv A B s x :
  Pi0 A B s ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi0 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_pi1_inv A B s x :
  Pi1 A B s ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi1 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_lam0_inv A m x s :
  Lam0 A m s ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam0 A' m' s.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1[A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sta_red_lam1_inv A m x s :
  Lam1 A m s ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam1 A' m' s.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1[A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma sta_red_sig0_inv A B s x :
  Sig0 A B s ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Sig0 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_sig1_inv A B s x :
  Sig1 A B s ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Sig1 A' B' s.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_pair0_inv m n s x :
  Pair0 m n s ~>* x ->
  exists m' n',
    m ~>* m' /\ n ~>* n' /\ x = Pair0 m' n' s.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_pair1_inv m n s x :
  Pair1 m n s ~>* x ->
  exists m' n',
    m ~>* m' /\ n ~>* n' /\ x = Pair1 m' n' s.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_bool_inv x : Bool ~>* x -> x = Bool.
Proof.
  elim=>//.
  move=>y z rd e st. subst.
  inv st.
Qed.

Lemma sta_red_tt_inv x : TT ~>* x -> x = TT.
Proof.
  elim=>//.
  move=>y z rd e st. subst.
  inv st.
Qed.

Lemma sta_red_ff_inv x : FF ~>* x -> x = FF.
Proof.
  elim=>//.
  move=>y z rd e st. subst.
  inv st.
Qed.

Lemma sta_red_id_inv A m n x :
  Id A m n ~>* x ->
  exists A' m' n',
    A ~>* A' /\ m ~>* m' /\ n ~>* n' /\ x = Id A' m' n'.
Proof.
  elim.
  exists A. exists m. exists n=>//.
  move=>y z rd[A'[m'[n'[r1[r2[r3 e]]]]]] st; subst.
  inv st.
  exists A'0. exists m'. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sta_red_refl_inv m x :
  Refl m ~>* x ->
  exists m', m ~>* m' /\ x = Refl m'.
Proof.
  elim.
  exists m=>//.
  move=>y z rd[m'[r e]] st; subst.
  inv st. exists m'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma sort_inj s1 s2 l1 l2 :
  Sort s1 l1 === Sort s2 l2 -> s1 = s2 /\ l1 = l2.
Proof.
  move/church_rosser=>[x/sta_red_sort_inv->/sta_red_sort_inv[->]]//.
Qed.

Lemma pi0_inj A A' B B' s s' :
  Pi0 A B s === Pi0 A' B' s' ->
    A === A' /\ B === B' /\ s = s'.
Proof.
  move/church_rosser=>
    [x/sta_red_pi0_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_pi0_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
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
    [x/sta_red_pi1_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_pi1_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
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
    [x/sta_red_sig0_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_sig0_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
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
    [x/sta_red_sig1_inv[A1[B1[rA1[rB1->]]]]
      /sta_red_sig1_inv[A2[B2[rA2[rB2[]]]]]] eA eB es; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma id_inj A A' m m' n n' :
  Id A m n === Id A' m' n' ->
    A === A' /\ m === m' /\ n === n'.
Proof.
  move/church_rosser=>
    [x/sta_red_id_inv[A1[m1[n1[rA1[rm1[rn1->]]]]]]
      /sta_red_id_inv[A2[m2[n2[rA2[rm2[rn2[]]]]]]]] eA em en; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rm1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rn1.
  apply: conv_sym. by apply: star_conv.
Qed.

Ltac red_inv m H :=
  match m with
  | Var   => apply sta_red_var_inv in H
  | Sort  => apply sta_red_sort_inv in H
  | Pi0   => apply sta_red_pi0_inv in H
  | Pi1   => apply sta_red_pi1_inv in H
  | Lam0  => apply sta_red_lam0_inv in H
  | Lam1  => apply sta_red_lam1_inv in H
  | Sig0  => apply sta_red_sig0_inv in H
  | Sig1  => apply sta_red_sig1_inv in H
  | Pair0 => apply sta_red_pair0_inv in H
  | Pair1 => apply sta_red_pair1_inv in H
  | Bool  => apply sta_red_bool_inv in H
  | TT    => apply sta_red_tt_inv in H
  | FF    => apply sta_red_ff_inv in H
  | Id    => apply sta_red_id_inv in H
  | Refl  => apply sta_red_refl_inv in H
  end.

Ltac solve_conv' :=
  unfold not; intros;
  match goal with
  | [ H : _ === _ |- _ ] =>
    apply church_rosser in H; inv H
  end;
  repeat match goal with
  | [ H : sta_red (?m _) _ |- _ ]         => red_inv m H
  | [ H : sta_red (?m _ _) _ |- _ ]       => red_inv m H
  | [ H : sta_red (?m _ _ _) _ |- _ ]     => red_inv m H
  | [ H : sta_red (?m _ _ _ _) _ |- _ ]   => red_inv m H
  | [ H : sta_red (?m _ _ _ _ _) _ |- _ ] => red_inv m H
  | [ H : sta_red ?m _ |- _ ]             => red_inv m H
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
