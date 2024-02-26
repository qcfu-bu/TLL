From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_csubst sta_subst sta_cren.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sta_agree_csubst (σ : var -> term) : Prop :=
  forall x, exists c, σ x = CVar c. 

Definition csubst_ren (σ : var -> term) :=
  fun x => match σ x with CVar y => y | _ => 0 end.

Lemma sta_csubst_cren m (σ : var -> term) :
  sta_agree_csubst σ -> cren (csubst_ren σ) m = csubst σ m.
Proof with eauto.
  move=>agr.
  elim: m σ agr=>//=...
  { move=>A ihA B ihB s σ agr. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ agr. rewrite ihA... rewrite ihB... }
  { move=>A ihA m ihm s σ agr. rewrite ihA... rewrite ihm... }
  { move=>A ihA m ihm s σ agr. rewrite ihA... rewrite ihm... }
  { move=>m ihm n ihn σ agr. rewrite ihm... rewrite ihn... }
  { move=>m ihm n ihn σ agr. rewrite ihm... rewrite ihn... }
  { move=>A ihA B ihB s σ agr. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ agr. rewrite ihA... rewrite ihB... }
  { move=>m ihm n ihn s σ agr. rewrite ihm... rewrite ihn... }
  { move=>m ihm n ihn s σ agr. rewrite ihm... rewrite ihn... }
  { move=>A ihA m ihm n ihn σ agr. rewrite ihA... rewrite ihm... rewrite ihn... }
  { move=>A ihA m ihm σ agr. rewrite ihA... rewrite ihm... }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2 σ agr.
    rewrite ihA... rewrite ihm... rewrite ihn1... rewrite ihn2... }
  { move=>A ihA σ agr. rewrite ihA... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm n ihn σ agr. rewrite ihm... rewrite ihn... }
  { move=>r A ihA B ihB σ agr. rewrite ihA... rewrite ihB... }
  { move=>r A ihA B ihB σ agr. rewrite ihA... rewrite ihB... }
  { move=>r A ihA σ agr. rewrite ihA... }
  { move=>x σ agr. rewrite/csubst_ren. by have[c->]:=agr x. }
  { move=>A ihA m ihm σ agr. rewrite ihA... rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
  { move=>m ihm σ agr. rewrite ihm... }
Qed.

Lemma sta_csubstitution Γ m A σ :
  Γ ⊢ m : A -> sta_agree_csubst σ -> Γ ⊢ csubst σ m : A.
Proof with eauto using sta_type.
  move=>ty agr.
  have e:=sta_csubst_cren m agr.
  have:=sta_crename (csubst_ren σ) ty.
  by rewrite e.
Qed.

Lemma sta_csubst_comm σ1 σ2 m :
  sta_agree_csubst σ1 ->
  cren_subst_agree σ2 σ2 (csubst_ren σ1) ->
  (csubst σ1 m).[σ2] = csubst σ1 m.[σ2].
Proof with eauto.
  move=>agr1 agr2.
  have<-:=sta_csubst_cren m agr1.
  have<-:=sta_csubst_cren m.[σ2] agr1.
  erewrite term_cren_subst...
Qed.

Lemma sta_csubst_comp σ ξ m : 
  sta_agree_csubst σ -> (csubst σ m).[ren ξ] = csubst σ m.[ren ξ].
Proof with eauto.
  elim: m σ ξ...
  all: try solve[intros; asimpl; autorew; eauto].
  move=>x σ ξ agr. asimpl.
  by have[c->]:=agr x.
Qed.

Definition sta_anti_csubst (σ : var -> term) :=
  forall x σ', sta_agree_csubst σ' -> σ x = csubst σ' (σ x).

Lemma sta_anti_csubst_up σ :
  sta_anti_csubst σ -> sta_anti_csubst (up σ).
Proof with eauto.
  move=>agr[|x]σ' agr'; asimpl. by simpl.
  have h:=agr x σ' agr'.
  rewrite-> h at 1.
  rewrite sta_csubst_comp...
Qed.

Lemma sta_csubst_comp' σ σ' m : 
  sta_agree_csubst σ ->
  sta_anti_csubst σ' ->
  (csubst σ m).[σ'] = csubst σ m.[σ'].
Proof with eauto using sta_anti_csubst_up.
  elim: m σ σ'...
  all: try solve[intros; asimpl; autorew; eauto].
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA B ihB s σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>A ihA m ihm n ihn σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihm... rewrite ihn... }
  { move=>A ihA m ihm σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihm... }
  { move=>A ihA m ihm n1 ihn1 n2 ihn2 σ σ' agr1 agr2. asimpl.
    rewrite ihA... rewrite ihm... rewrite ihn1... rewrite ihn2... }
  { move=>m ihm n ihn σ σ' agr1 agr2. asimpl. rewrite ihm... rewrite ihn... }
  { move=>r A ihA B ihB σ1 σ2 agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>r A ihA B ihB σ1 σ2 agr1 agr2. asimpl. rewrite ihA... rewrite ihB... }
  { move=>x σ σ' agr1 agr2. asimpl. by have[c->]:=agr1 x. }
  { move=>A ihA m ihm σ σ' agr1 agr2. asimpl. rewrite ihA... rewrite ihm... }
Qed.
