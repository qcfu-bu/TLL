From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive inst0 : term -> term -> Prop :=
| inst0_var x :
  inst0 (Var x) (Var x)
| inst0_sort s :
  inst0 (Sort s) (Sort s)
| inst0_pi0 A A' B B' s :
  inst0 A A' ->
  inst0 B B' ->
  inst0 (Pi0 A B s) (Pi0 A' B' s)
| inst0_pi1 A A' B B' s :
  inst0 A A' ->
  inst0 B B' ->
  inst0 (Pi1 A B s) (Pi1 A' B' s)
| inst0_lam0 A A' m m' s :
  inst0 A A' ->
  inst0 m m' ->
  inst0 (Lam0 A m s) (Lam0 A' m' s)
| inst0_lam1 A A' m m' s :
  inst0 A A' ->
  inst0 m m' ->
  inst0 (Lam1 A m s) (Lam1 A' m' s)
| inst0_app m m' n n' :
  inst0 m m' ->
  inst0 n n' ->
  inst0 (App m n) (App m' n')
| inst0_unit :
  inst0 Unit Unit
| inst0_it :
  inst0 It It
| inst0_nat :
  inst0 Nat Nat
| inst0_num n :
  inst0 (Num n) (Num n)
| inst0_rand0 :
  inst0 Rand Rand
| inst0_rand1 n :
  inst0 (Lam1 Unit (Num n) U) Rand
| inst0_box :
  inst0 Box Box.

Inductive inst : term -> term -> Prop :=
| inst_nil a b c : a === b -> inst0 b c -> inst a c
| inst_cons a b c d : inst a b -> b === c -> inst0 c d -> inst a d.
Infix "<:" := inst (at level 50, no associativity).

Lemma inst0_refl A : inst0 A A.
Proof with eauto using inst0. elim: A... Qed.

Lemma inst0_trans a b c : inst0 a b -> inst0 b c -> inst0 a c.
Proof with eauto using inst0.
  move=>ist. elim: ist c=>{a b}...
  { move=>A A' B B' s istA ihA istB ihB c ist. inv ist... }
  { move=>A A' B B' s istA ihA istB ihB c ist. inv ist... }
  { move=>A A' m m' s istA ihA istm ihm c ist. inv ist... }
  { move=>A A' m m' s istA ihA istm ihm c ist. inv ist...
    inv istm. inv istA. apply: inst0_rand1. }
  { move=>m m' n n' istm ihm istn ihn c ist. inv ist... }
  { move=>n c ist. inv ist... }
Qed.

Lemma inst_refl A : inst A A.
Proof with eauto using inst0_refl. apply: inst_nil... Qed.

Lemma inst_trans A B C : A <: B -> B <: C -> A <: C.
Proof with eauto using inst, inst_refl.
  move=>ist1 ist2. elim: ist2 A ist1=>{B C}...
Qed.

Lemma inst0_subst A B σ : inst0 A B -> inst0 A.[σ] B.[σ].
Proof with eauto using inst0, inst0_refl.
  move=>ist. elim: ist σ=>{A B}...
Qed.

Definition isubst (σ σ' : var -> term) := forall x, inst0 (σ x) (σ' x).

Lemma isubst_refl σ : isubst σ σ.
Proof with eauto using inst0, inst0_refl.
  move=>x. elim: x...
Qed.

Lemma isubst0 m m' : inst0 m m' -> isubst (m .: ids) (m' .: ids).
Proof with eauto using inst0. move=>ist x. elim: x m m' ist... Qed.

Lemma isubst0_uniq σ m' : isubst σ (m' .: ids) -> exists m, inst0 m m'.
Proof with eauto.
  move=>h. have:=h 0. asimpl=>{}h...
Qed.

Lemma isubst_up σ σ' :
  isubst σ σ' -> isubst (up σ) (up σ').
Proof with eauto using inst0, inst0_refl.
  move=>h x. elim: x σ σ' h.
  { move=>σ σ' h. asimpl... }
  { move=>n ih σ σ' h. asimpl.
    apply: inst0_subst... }
Qed.

Lemma inst0_compat m σ σ' : isubst σ σ' -> inst0 m.[σ] m.[σ'].
Proof with eauto using inst0, isubst_up.
  elim: m σ σ'.
  { move=>x σ σ' sb. asimpl... }
  { move=>s σ σ' sb. asimpl... }
  { move=>A ihA B ihB s σ σ' sb. asimpl... }
  { move=>A ihA B ihB s σ σ' sb. asimpl... }
  { move=>A ihA m ihm s σ σ' sb. asimpl... }
  { move=>A ihA m ihm s σ σ' sb. asimpl... }
  { move=>m ihm n ihn σ σ' sb. asimpl... }
  { move=>σ σ' sb. asimpl... }
  { move=>σ σ' sb. asimpl... }
  { move=>σ σ' sb. asimpl... }
  { move=>i σ σ' sb. asimpl... }
  { move=>σ σ' sb. asimpl... }
  { move=>σ σ' sb. asimpl... }
Qed.

Lemma inst0_beta m n n' : inst0 n n' -> inst0 m.[n/] m.[n'/].
Proof.
  move=>ist.
  apply: inst0_compat.
  exact: isubst0.
Qed.

Lemma inst0_isubst_inv a x σ' :
  inst0 a (σ' x) -> exists σ, a = σ x /\ isubst σ σ'.
Proof with eauto using inst0_refl.
  move=>ist.
  exists (fun n => if n == x then a else σ' n).
  split.
  by rewrite eq_refl.
  move=>y.
  case_eq (y == x)=>/eqP e... subst...
Qed.

(* Lemma inst0_subst_inv a b' σ' : *)
(*   inst0 a b'.[σ'] -> exists b σ, a = b.[σ] /\ inst0 b b' /\ isubst σ σ'. *)
(* Proof with eauto using inst0, inst0_refl, isubst_refl. *)
(*   move e:(b'.[σ'])=>x ist. *)
(*   elim: ist b' σ' e=>{a x}. *)
(*   { move=>x b' σ' e. exists b'. exists σ'. repeat split... } *)
(*   { move=>s b' σ' e. exists b'. exists σ'. repeat split... } *)
(*   { move=>A A' B B' s istA ihA istB ihB b' σ' e. *)
(*     destruct b'; simpl in e; inv e. *)
(*     { exists (Var x). exists (fun n => if n == x then Pi0 A B s else σ' n)=>/=. repeat split... *)
(*       by rewrite eq_refl. *)
(*       move=>y. *)
(*       case_eq (y == x)=>/eqP e... subst. *)
(*       rewrite H0... } *)
(*     { *)
(*       have[A'[σA[eA[istA' sbA]]]]:=ihA _ _ erefl. *)
(*       have[B'[σB[eB[istB' sbB]]]]:=ihB _ _ erefl. *)
(*     } *)
(*   } *)


Lemma inst_subst A B σ : A <: B -> A.[σ] <: B.[σ].
Proof with eauto.
  move=>ist. elim: ist σ=>{A B}...
  { move=>a b c eq ist σ.
    apply: inst_nil.
    apply: sta_conv_subst...
    apply: inst0_subst... }
  { move=>a b c d ist1 ih eq ist2 σ.
    apply: inst_cons.
    apply: ih.
    apply: sta_conv_subst...
    apply: inst0_subst... }
Qed.

(* Lemma inst_step a b c d : *)
(*   a === b -> inst0 b c -> d ~> c -> *)
(*   exists x, a === x /\ inst0 x d. *)
(* Proof with eauto using inst0, inst0_refl. *)
(*   move=>eq ist st. elim: st a b eq ist=>{d}. *)
(*   { move=>A A' B s st ih a b eq ist. inv ist. *)
(*     have[A1[eq1 ist1]]:=ih _ _ (convR _ _) H2. *)
(*     exists (Pi0 A1 B0 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_pi0... } *)
(*   { move=>A A' B s st ih a b eq ist. inv ist. *)
(*     have[A1[eq1 ist1]]:=ih _ _ (convR _ _) H2. *)
(*     exists (Pi1 A1 B0 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_pi1... } *)
(*   { move=>A B B' s st ih a b eq ist. inv ist. *)
(*     have[B1[eq1 ist1]]:=ih _ _ (convR _ _) H4. *)
(*     exists (Pi0 A0 B1 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_pi0... } *)
(*   { move=>A B B' s st ih a b eq ist. inv ist. *)
(*     have[B1[eq1 ist1]]:=ih _ _ (convR _ _) H4. *)
(*     exists (Pi1 A0 B1 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_pi1... } *)
(*   { move=>A A' m s st ih a b eq ist. inv ist. *)
(*     have[A1[eq1 ist1]]:=ih _ _ (convR _ _) H2. *)
(*     exists (Lam0 A1 m0 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_lam0... } *)
(*   { move=>A A' m s st ih a b eq ist. inv ist. *)
(*     have[A1[eq1 ist1]]:=ih _ _ (convR _ _) H2. *)
(*     exists (Lam1 A1 m0 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_lam1... } *)
(*   { move=>A m m' s st ih a b eq ist. inv ist. *)
(*     have[m1[eq1 ist1]]:=ih _ _ (convR _ _) H4. *)
(*     exists (Lam0 A0 m1 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_lam0... } *)
(*   { move=>A m m' s st ih a b eq ist. inv ist. *)
(*     have[m1[eq1 ist1]]:=ih _ _ (convR _ _) H4. *)
(*     exists (Lam1 A0 m1 s). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_lam1... } *)
(*   { move=>m m' n st ih a b eq ist. inv ist. *)
(*     have[m1[eq1 ist1]]:=ih _ _ (convR _ _) H2. *)
(*     exists (App m1 n0). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_app... } *)
(*   { move=>m n n' st ih a b eq ist. inv ist. *)
(*     have[n1[eq1 ist1]]:=ih _ _ (convR _ _) H3. *)
(*     exists (App m0 n1). split... *)
(*     apply: conv_trans. *)
(*     apply: eq. *)
(*     apply: sta_conv_app... } *)
(*   { move=>A m n s a b eq ist. *)
(*   } *)

Lemma inst_step a b c d :
  a === b -> inst0 b c -> c ~> d ->
  exists x, a === x /\ inst0 x d.
Proof with eauto using inst0_refl.
  move=>eq ist. elim: ist a d eq=>{b c}.
  { move=>x a d eq1 eq2. inv eq2. }
  { move=>s a d eq1 eq2. inv eq2. }
  { move=>A A' B B' s istA ihA istB ihB a d eq1 eq2. inv eq2.
    { have[A1[eq2 istA']]:=ihA _ _ (convR _ _) H3.
      exists (Pi0 A1 B s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_pi0...
      constructor... }
    { have[B1[eq2 istB']]:=ihB _ _ (convR _ _) H3.
      exists (Pi0 A B1 s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_pi0...
      constructor... } }
  { move=>A A' B B' s istA ihA istB ihB a d eq1 eq2. inv eq2.
    { have[A1[eq2 istA']]:=ihA _ _ (convR _ _) H3.
      exists (Pi1 A1 B s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_pi1...
      constructor... }
    { have[B1[eq2 istB']]:=ihB _ _ (convR _ _) H3.
      exists (Pi1 A B1 s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_pi1...
      constructor... } }
  { move=>A A' m m' s istA ihA istm ihm a d eq1 eq2. inv eq2.
    { have[A1[eq2 istA']]:=ihA _ _ (convR _ _) H3.
      exists (Lam0 A1 m s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_lam0...
      constructor... }
    { have[m1[eq2 istm']]:=ihm _ _ (convR _ _) H3.
      exists (Lam0 A m1 s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_lam0...
      constructor... } }
  { move=>A A' m m' s istA ihA istm ihm a d eq1 eq2. inv eq2.
    { have[A1[eq2 istA']]:=ihA _ _ (convR _ _) H3.
      exists (Lam1 A1 m s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_lam1...
      constructor... }
    { have[m1[eq2 istm']]:=ihm _ _ (convR _ _) H3.
      exists (Lam1 A m1 s). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_lam1...
      constructor... } }
  { move=>m m' n n' istm ihm istn ihn a d eq1 st. inv st.
    { have[m1[rd2 istm']]:=ihm _ _ (convR _ _) H2.
      exists (App m1 n). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_app...
      constructor... }
    { have[n1[eq2 istn']]:=ihn _ _ (convR _ _) H2.
      exists (App m n1). split.
      apply: conv_trans.
      apply: eq1.
      apply: sta_conv_app...
      constructor... }
    { inv istm.
      exists m1.[n/]. split.
      apply: conv_trans.
      apply: eq1.
      apply: conv1.
      apply: sta_step_beta0.
      apply: inst0_trans.
      apply: inst0_subst...
      apply: inst0_beta... }
    { inv istm.
      exists m1.[n/]. split.
      apply: conv_trans.
      apply: eq1.
      apply: conv1.
      apply: sta_step_beta1.
      apply: inst0_trans.
      apply: inst0_subst...
      apply: inst0_beta... } }
  { move=>a d rd st. inv st. }
  { move=>a d rd st. inv st. }
  { move=>a d rd st. inv st. }
  { move=>n a d rd st. inv st. }
  { move=>a d rd st. inv st. }
  { move=>n a d rd st. inv st. }
  { move=>a d rd st. inv st. }
Qed.

Lemma inst_red a b c d :
  a === b -> inst0 b c -> c ~>* d ->
  exists x, a === x /\ inst0 x d.
Proof with eauto using inst0_refl.
  move=>eq ist rd.
  elim: rd a b eq ist=>{d}.
  { move=>a b eq ist. exists b... }
  { move=>y z eq1 ih st a b eq2 ist.
    have[x[eqx istx]]:=ih _ _ eq2 ist.
    apply: inst_step... }
Qed.

(* Lemma inst_conv a b c d : *)
(*   a === b -> inst0 b c -> c === d -> *)
(*   exists x, a === x /\ inst0 x d. *)
(* Proof with eauto using inst0_refl. *)
(*   move=>eq1 ist eq2. *)
(*   elim: eq2 a b eq1 ist=>{d}. *)
(*   { move=>a b eq ist. exists b... } *)
(*   { move=>y z eq1 ih st a b eq2 ist. *)
(*     have[x[eqx istx]]:=ih _ _ eq2 ist. *)
(*     apply: inst_step... } *)
(*   { move=>y z eq1 ih st a b eq2 ist. *)
(*     have[x[eqx istx]]:=ih _ _ eq2 ist. *)
(*   } *)
(* Qed. *)


(* Lemma inst_singular a c : *)
(*   a <: c -> exists b, a === b /\ inst0 b c. *)
(* Proof with eauto. *)
(*   move=>ist. elim: ist=>{a c}... *)
(*   move=>a b c d ist[b0[eq1 ist1]] eq2 ist2. *)
(*   have[x rd1 rd2]:=church_rosser eq2. *)
(*   have[x0[eq3 ist3]]:=inst_red eq1 ist1 rd1. *)
(*   have[x1[eq4 ist4]]:=inst_red eq2 ist2 (starR _ _). *)


Lemma pi0_inst_inj A1 A2 B1 B2 s1 s2 :
  Pi0 A1 B1 s1 <: Pi0 A2 B2 s2 -> A1 <: A2 /\ B1 <: B2 /\ s1 = s2. 
Proof with eauto.
  move e1:(Pi0 A1 B1 s1)=>x.
  move e2:(Pi0 A2 B2 s2)=>y ist.
  elim: ist A1 A2 B1 B2 s1 s2 e1 e2=>{x y}.
  { move=>a b c eq ist A1 A2 B1 B2 s1 s2 e1 e2; subst.
    inv ist.
    have[eq1[eq2 e]]:=pi0_inj eq; subst.
    repeat split.
    apply: inst_nil...
    apply: inst_nil... }
  { move=>a b c d ist1 ih eq ist2 A1 A2 B1 B2 s1 s2 e1 e2; subst.
    inv ist2.
    have[x rd1 rd2]:=church_rosser eq.
    have[A'[B'[rdA[rdB e]]]]:=sta_red_pi0_inv rd2. subst.
  }


