From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type ptr_heap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope heap_scope.

Definition pad (H1 H2 : heap) : Prop :=
  exists H0, H0 ▷ U /\ domm H1 :#: domm H0 /\ H2 = unionm H1 H0.

Definition free (H1 : heap) l m (H2 : heap) : Prop := 
  match H1 l with
  | Some (n, U) => m = n /\ H2 = H1
  | Some (n, L) => m = n /\ H2 = remm H1 l
  | None => false
  end.

Reserved Notation "H ; m ~ n" (at level 50, m, n at next level).

Inductive resolve : heap -> term -> term -> Prop :=
| resolve_var H x :
  H ▷ U ->
  H ; Var x ~ Var x
| resolve_lam0 H m m' s :
  H ▷ s ->
  H ; m ~ m' ->
  H ; Lam0 Box m s ~ Lam0 Box m' s
| resolve_lam1 H m m' s :
  H ▷ s ->
  H ; m ~ m' ->
  H ; Lam1 Box m s ~ Lam1 Box m' s
| resolve_app0 H m m' :
  H ; m ~ m' ->
  H ; App m Box ~ App m' Box
| resolve_app1 H1 H2 H m m' n n' :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; App m n ~ App m' n'
| resolve_pair0 H m m' t :
  H ; m ~ m' ->
  H ; Pair0 m Box t ~ Pair0 m' Box t
| resolve_pair1 H1 H2 H m m' n n'  t :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; Pair1 m n t ~ Pair1 m' n' t
| resolve_letin H1 H2 H m m' n n' :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; LetIn Box m n ~ LetIn Box m' n'
| resolve_tt H :
  H ▷ U ->
  H ; TT ~ TT
| resolve_ff H :
  H ▷ U ->
  H ; FF ~ FF
| resolve_ifte H1 H2 H m m' n1 n1' n2 n2' :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n1 ~ n1' ->
  H2 ; n2 ~ n2' ->
  H ; Ifte Box m n1 n2 ~ Ifte Box m' n1' n2'
| resolve_rw H m m' :
  H ; m ~ m' ->
  H ; Rw Box m Box ~ Rw Box m' Box
| resolve_ptr H H' l m m' :
  free H l m H' ->
  H' ; m ~ m' ->
  H ; Ptr l ~ m'
where "H ; m ~ n" := (resolve H m n).

Inductive resolved : term -> Prop :=
| resolved_var x :
  resolved (Var x)
| resolved_lam0 m s :
  resolved m ->
  resolved (Lam0 Box m s)
| resolved_lam1 m s :
  resolved m ->
  resolved (Lam1 Box m s)
| resolved_app0 m :
  resolved m ->
  resolved (App m Box)
| resovled_app1 m n :
  resolved m ->
  resolved n ->
  resolved (App m n)
| resolved_pair0 m t :
  resolved m ->
  resolved (Pair0 m Box t)
| resolved_pair1 m n t :
  resolved m ->
  resolved n ->
  resolved (Pair1 m n t)
| resolved_letin m n :
  resolved m ->
  resolved n ->
  resolved (LetIn Box m n)
| resolved_tt :
  resolved TT
| resolved_ff :
  resolved FF
| resolved_ifte m n1 n2 :
  resolved m ->
  resolved n1 ->
  resolved n2 ->
  resolved (Ifte Box m n1 n2)
| resolved_rw m :
  resolved m ->
  resolved (Rw Box m Box).

Lemma pad_refl H : pad H H.
Proof.
  rewrite/pad. exists emptym. rsplit.
  apply/fdisjointP=>x _.
  apply/dommP=>[[v]]. rewrite emptymE//.
  apply eq_fmap=>x.
  rewrite unionmE.
  by case_eq (H x).
Qed.

Lemma pad_setm H m l : l \notin domm H -> pad H (setm H l (m, U)).
Proof.
  rewrite/pad.
  exists (mkfmap [:: (l, (m, U))]). rsplit.
  move=>x. rewrite mkfmapE=>/=. by case (x == l).
  rewrite fdisjointC. apply/fdisjointP=>x.
  rewrite domm_mkfmap. rewrite/unzip1=>/=. rewrite in_fset1.
  move=>/eqP e. by subst.
  apply eq_fmap=>x.
  rewrite setmE.
  rewrite unionmE.
  move: H0=>/dommPn H0.
  case_eq (x == l)=>[/eqP e|e]; subst.
  rewrite H0=>//=. by rewrite setmE eq_refl.
  case_eq (H x); rmatch_case. rewrite setmE e.
  by rewrite emptymE.
Qed.

Lemma pad_key H H' s : pad H H' -> H ▷ s -> H' ▷ s.
Proof.
  rewrite/pad.
  move=>[H0[k1[d0->]]] k2 l. move: (k1 l). move: (k2 l).
  rmatch_case.
  { rewrite unionmE in H3.
    rewrite H10 in H3. simpl in H3. inv H3. }
  { rewrite unionmE in H3.
    rewrite H8 in H3. simpl in H3. inv H3. }
  { rewrite unionmE in H4.
    rewrite H8 in H4. simpl in H4.
    rewrite H4 in H7. inv H7. }
  { rewrite unionmE in H4.
    rewrite H6 in H4. simpl in H4.
    rewrite H4 in H5. inv H5. }
Qed.

Lemma pad_merge H1 H2 H Hp :
  pad H Hp -> H1 ∘ H2 => H ->
  exists H1p H2p, pad H1 H1p /\ pad H2 H2p /\ H1p ∘ H2p => Hp.
Proof.
  move=>[H0[k0[d0 e0]]] mrg; subst.
  exists (unionm H1 H0). exists (unionm H2 H0). rsplit.
  { exists H0. rsplit=>//.
    apply/fdisjointP=>x h.
    have{}h:=hmrg_domm mrg h.
    move: d0=>/fdisjointP h0.
    exact: h0. }
  { exists H0. rsplit=>//.
    apply/fdisjointP=>x h.
    have{}h:=hmrg_domm (hmrg_sym mrg) h.
    move: d0=>/fdisjointP h0.
    exact: h0. }
  { exact: hmrg_unionm. }
Qed.

Lemma ptr_resolve_resolved H m m' : H ; m ~ m' -> resolved m'.
Proof with eauto using resolved. elim=>{H m m'}... Qed.

Reserved Notation "H ; x ~ y ~ z : A" (at level 50, x, y, z, A at next level).
Inductive ptr_well_resolved :
  heap -> term -> term -> term -> term -> Prop :=
| Ptr_well_resolved H x y z A :
  nil ; nil ⊢ x ~ y : A ->
  H ; z ~ y ->
  H ; x ~ y ~ z : A
where "H ; x ~ y ~ z : A" := (ptr_well_resolved H x y z A).

Lemma free_domm H1 H2 l1 l2 m :
  free H1 l1 m H2 -> l2 \notin domm H1 -> l2 \notin domm H2.
Proof.
  move=>fr/dommPn h. apply/dommPn.
  move:fr. rewrite/free.
  rmatch_case.
  rewrite remmE.
  case_eq (l2 == l1)=>//.
Qed.

Lemma free_setm H1 H2 l1 l2 m n :
  l1 \notin domm H1 ->
  free H1 l2 m H2 ->
  free (setm H1 l1 (n, U)) l2 m (setm H2 l1 (n, U)).
Proof.
  move=>/dommPn h. rewrite/free.
  rewrite setmE. case_eq (l2 == l1); rmatch_case.
  move: H4=>/eqP e; subst. rewrite H3 in h. by inv h.
  move: H4=>/eqP e; subst. rewrite H3 in h. by inv h.
  move: H4=>/eqP e; subst. rewrite H3 in h. by inv h.
  apply/eq_fmap=>l. rewrite!setmE. rewrite!remmE. rewrite setmE.
  case_eq (l == l1); case_eq (l == l2)=>//=/eqP e1/eqP e2; subst.
  rewrite h in H3. by inv H3.
Qed.

Lemma free_unionm H0 H1 H2 l m :
  domm H0 :#: domm H1 ->
  free H1 l m H2 ->
  free (unionm H1 H0) l m (unionm H2 H0).
Proof.
  move=>d0. rewrite/free. rewrite unionmE.
  case_eq (H1 l)=>/=; rmatch_case.
  apply eq_fmap=>x.
  rewrite!unionmE. rewrite!remmE. rewrite!unionmE.
  case_eq (x == l)=>//=/eqP e. subst.
  rewrite fdisjointC in d0.
  move: d0=>/fdisjointP d0.
  apply/dommPn.
  apply: d0.
  apply/dommP. by exists (t, L).
Qed.

Lemma resolve_wkU H m m' n l :
  H ; m ~ m' -> l \notin domm H -> (setm H l (n, U)) ; m ~ m'.
Proof with eauto using resolve, hkey_setm.
  move=>rs. elim: rs n l=>{H m m'}...
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn n0 l h.
    have[h1 h2]:=hmrg_none mrg h. econstructor.
    apply: hmrg_setmU...
    apply: ihm...
    apply: ihn... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn n0 l h.
    have[h1 h2]:=hmrg_none mrg h. econstructor.
    apply: hmrg_setmU...
    apply: ihm...
    apply: ihn... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn n0 l h.
    have[h1 h2]:=hmrg_none mrg h. econstructor.
    apply: hmrg_setmU...
    apply: ihm...
    apply: ihn... }
  { move=>H1 H2 H m m' n1 n1' n2 n2' mrg rsm ihm rsn1 ihn1 rsn2 ihn2 n l h.
    have[h1 h2]:=hmrg_none mrg h. econstructor.
    apply: hmrg_setmU...
    apply: ihm...
    apply: ihn1...
    apply: ihn2... }
  { move=>H H' l m m' fr rsm ihm n l0 h. econstructor.
    2:{ apply: ihm. shelve. apply: free_domm... }
    by apply: free_setm. }
Qed.

Lemma resolve_pad H H' m m' :
  pad H H' -> H ; m ~ m' -> H' ; m ~ m'.
Proof with eauto using resolve, resolve_wkU, hkey_unionm.
  move=>[H0[k0[d0 e]]] rsm. subst.
  elim: rsm d0=>{H m m'}...
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn d0. econstructor.
    apply: hmrg_unionm...
    { apply: ihm...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm... }
    { apply: ihn...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm.
      apply: hmrg_sym...
      exact: h. } }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn d0. econstructor.
    apply: hmrg_unionm...
    { apply: ihm...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm... }
    { apply: ihn...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm.
      apply: hmrg_sym...
      exact: h. } }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn d0. econstructor.
    apply: hmrg_unionm...
    { apply: ihm...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm... }
    { apply: ihn...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm.
      apply: hmrg_sym...
      exact: h. } }
  { move=>H1 H2 H m m' n1 n1' n2 n2' mrg rsm ihm rsn1 ihn1 rsn2 ihn2 d0.
    econstructor. apply: hmrg_unionm...
    { apply: ihm...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm... }
    { apply: ihn1...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm.
      apply: hmrg_sym...
      exact: h. }
    { apply: ihn2...
      apply/fdisjointP=>x h.
      move: d0=>/fdisjointP d0.
      apply: d0.
      apply: hmrg_domm.
      apply: hmrg_sym...
      exact: h. } }
  { move=>H H' l m m' fr rsm ih d0. econstructor.
    apply: free_unionm...
    by rewrite fdisjointC.
    apply: ih.
    rewrite fdisjointC.
    apply/fdisjointP=>x h.
    rewrite fdisjointC in d0.
    move: d0=>/fdisjointP d0.
    have{d0}h:=d0 _ h.
    apply: free_domm... }
Qed.

Lemma resolve_era_refl H Γ Δ m n A :
  Γ ; Δ ⊢ m ~ n : A -> H ▷ U -> H ; n ~ n.
Proof with eauto 6 using resolve, hkey_impure, hmrg_pure_refl.
  move=>er. elim: er H=>//{Γ Δ m n A}...
  { move=>Γ Δ A B m m' [|] k1 erm ihm k2... }
  { move=>Γ Δ A B m m' [|] t k1 erm ihm k2... }
Qed.

Lemma resolve_era_id H Γ Δ x y z A :
  Γ ; Δ ⊢ x ~ y : A -> H ; y ~ z -> y = z.
Proof with eauto using resolve.
  move=>ty. elim: ty H z=>//{Γ Δ x y A}...
  { move=>Γ Δ x s A wf shs dhs H z rs. inv rs... }
  { move=>Γ Δ A B m m' s k erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H6. }
  { move=>Γ Δ A B m m' s t k erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H6. }
  { move=>Γ Δ A B m m' n s erm ihm tyn H z rs. inv rs.
    { have->//:=ihm _ _ H3. }
    { inv H9. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn H z rs. inv rs.
    { have->//:=ihm _ _ H5. }
    { have->:=ihm _ _ H7.
      have->//:=ihn _ _ H9. } }
  { move=>Γ Δ A B m m' n t l tyS erm ihm tyn H z rs. inv rs.
    have->//:=ihm _ _ H5. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg tyS erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H9.
    have->//:=ihn _ _ H10. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t l mrg tyC erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H7.
    have->//:=ihn _ _ H9. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t l mrg tyC erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H7.
    have->//:=ihn _ _ H9. }
  { move=>Γ Δ wf k H z rs. inv rs... }
  { move=>Γ Δ wf k H z rs. inv rs... }
  { move=>Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s l
           mrg tyA erm ihm ern1 ihn1 ern2 ihn2 H z rs. inv rs.
    have->:=ihm _ _ H8.
    have->:=ihn1 _ _ H10.
    have->//:=ihn2 _ _ H11. }
  { move=>Γ Δ A B x x' P m n s l tyB erH ihH tyP H0 z rs. inv rs. f_equal... }
Qed.

Lemma free_inv H H' m n l t :
  free (setm H l (m, t)) l n H' ->
  m = n /\ match t with
          | U => setm H l (m, t) = H'
          | L => remm H l = H'
          end.
Proof with eauto.
  rewrite/free.
  rewrite setmE.
  rewrite eq_refl.
  case: t.
  { move=>[e1 e2]. by subst. }
  { move=>[e1 e2]. subst. split=>//.
    apply eq_fmap=>x.
    rewrite!remmE. rewrite!setmE.
    by case_eq (x == l). }
Qed.

Lemma free_merge H1 H2 H3 H l m :
  free H1 l m H3 -> H1 ∘ H2 => H ->
  exists H4, free H l m H4 /\ H3 ∘ H2 => H4.
Proof with eauto using free.
  rewrite/free.
  case_eq (H1 l)=>//.
  move=>[n[|]]e[e1 e2]mrg; subst.
  { have{}:=mrg l. rewrite e.
    case_eq (H2 l); case_eq (H l); rmatch_case.
    by exists H. }
  { have:=mrg l. rewrite e.
    case_eq (H2 l); case_eq (H l); rmatch_case.
    exists (remm H l). rsplit.
    move=>x. rewrite!remmE.
    case_eq (x == l)=>/eqP e0. subst. by rewrite H5.
    have:=mrg x. rmatch_case. }
Qed.

Lemma free_pure H H' m l : free H l m H' -> H ▷ U -> H' ▷ U.
Proof with eauto.
  rewrite/free.
  rmatch_case.
  exact: hkey_remm.
Qed.

Lemma free_subheap H H1 H2 H' H1' l m n :
  H1 ∘ H2 => H -> free H l m H' -> free H1 l n H1' -> m = n /\ H1' ∘ H2 => H'.
Proof with eauto.
  move=>mrg. have:=mrg l. rewrite/free.
  rmatch_case.
  move=>x. rewrite!remmE.
  case_eq (x == l)=>/eqP e; subst.
  by rewrite H5.
  have:=mrg x. rmatch_case.
Qed.

Lemma resolve_merge_pure H1 H2 H m m' :
  H1 ; m ~ m' -> H1 ∘ H2 => H -> H2 ▷ U -> H ; m ~ m'.
Proof with eauto using resolve, resolve_wkU.
  move=>rs. elim: rs H2 H=>{H1 m m'}...
  { move=>H x k1 H2 H0 mrg k2.
    constructor...
    apply: hmrg_pure... }
  { move=>H m m' s k1 rm ihm H2 H0 mrg k2.
    constructor...
    have->//:=hmrg_pureR mrg k2. }
  { move=>H m m' s k1 rm ihm H2 H0 mrg k2.
    constructor...
    have->//:=hmrg_pureR mrg k2. }
  { move=>H1 H2 H m m' n n' mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H1 H2 H m m' n n' t mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H1 H2 H m m' n n' mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H k1 H0 H3 mrg k2.
    have->:=hmrg_pureR mrg k2.
    constructor... }
  { move=>H k1 H0 H3 mrg k2.
    have->:=hmrg_pureR mrg k2.
    constructor... }
  { move=>H1 H2 H m m' n1 n1' n2 n2' mrg1 erm ihm ern1 ihn1 ern2 ihn2 H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=hmrg_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern1.
    apply: ern2. }
  { move=>H H' l m m' fr erm ihm H2 H0 mrg k.
    econstructor...
    have->//:=hmrg_pureR mrg k. }
Qed.

Lemma resolve_free H1 H2 H H' l m n :
  free H l m H' -> H1 ; Ptr l ~ n -> H1 ∘ H2 => H ->
  exists H1', H1' ∘ H2 => H' /\ H1' ; m ~ n.
Proof with eauto.
  move=>fr rs mrg. inv rs.
  have[->mrg']:=free_subheap mrg fr H4. exists H'0...
Qed.

Inductive nf : nat -> term -> Prop :=
| nf_var i x :
  x < i ->
  nf i (Var x)
| nf_lam0 i m s :
  nf i.+1 m ->
  nf i (Lam0 Box m s)
| nf_lam1 i m s :
  nf i.+1 m ->
  nf i (Lam1 Box m s)
| nf_app0 i m :
  nf i m ->
  nf i (App m Box)
| nf_app1 i m n :
  nf i m ->
  nf i n ->
  nf i (App m n)
| nf_pair0 i m t :
  nf i m ->
  nf i (Pair0 m Box t)
| nf_pair1 i m n t :
  nf i m ->
  nf i n ->
  nf i (Pair1 m n t)
| nf_letin i m n :
  nf i m ->
  nf i.+2 n ->
  nf i (LetIn Box m n)
| nf_tt i :
  nf i TT
| nf_ff i :
  nf i FF
| nf_ifte i m n1 n2 :
  nf i m ->
  nf i n1 ->
  nf i n2 ->
  nf i (Ifte Box m n1 n2)
| nf_rw i m :
  nf i m ->
  nf i (Rw Box m Box)
| nf_ptr i l :
  nf i (Ptr l).

Definition wr_heap (H : heap) : Prop :=
  forall l, match H l with
       | None => True
       | Some (Lam0 Box m s1, s2) => nf 1 m /\ s1 = s2
       | Some (Lam1 Box m s1, s2) => nf 1 m /\ s1 = s2
       | Some (Pair0 (Ptr _) Box s1, s2) => s1 = s2
       | Some (Pair1 (Ptr _) (Ptr _) s1, s2) => s1 = s2
       | Some (TT, s) => s = U
       | Some (FF, s) => s = U
       | _ => False
       end.

Lemma nf_typing Γ Δ m n A :
  Γ ; Δ ⊢ m ~ n : A -> nf (size Γ) n.
Proof with eauto using nf.
  elim=>//{Γ Δ m n A}...
  move=>Γ Δ x s A wf shs dhs.
  constructor.
  apply:sta_has_size shs.
Qed.

Lemma free_wr_nf H l m H' :
  free H l m H' -> wr_heap H -> nf 0 m.
Proof with eauto using nf.
  rewrite/free. rmatch_case.
  { have{H4}:=H4 l. rewrite H2. rmatch_case... }
  { have{H4}:=H4 l. rewrite H2. rmatch_case... }
Qed.

Lemma wr_merge H1 H2 H :
  H1 ∘ H2 => H -> wr_heap H1 -> wr_heap H2 -> wr_heap H.
Proof with eauto.
  move=>mrg wr1 wr2 l.
  have:=wr2 l. have:=wr1 l. have:=mrg l.
  case_eq (H1 l)=>[[m1[|]]|]e1.
  { case_eq (H2 l)=>[[m2[|]]|]e2//.
    case_eq (H l)=>[[m[|]]|]e[e3 e4]//. by subst. }
  { case_eq (H2 l)=>[[m2[|]]|]e2//.
    case_eq (H l)=>[[m[|]]|]e[e3 e4]//. by subst. }
  { case_eq (H2 l)=>[[m2[|]]|]e2//.
    case_eq (H l)=>[[m[|]]|]e[e3 e4]//. by subst.
    by case_eq (H l)=>[[m[|]]|]//. }
Qed.

Lemma wr_merge_inv H1 H2 H :
  H1 ∘ H2 => H -> wr_heap H -> wr_heap H1 /\ wr_heap H2.
Proof with eauto.
  move=>mrg wr. split.
  { move=>l.
    have:=wr l. have:=mrg l.
    case_eq (H l)=>[[m[|]]|]e.
    { case_eq (H1 l)=>[[m1[|]]|]e1//.
      case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//. by subst.
      by case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//. }
    { case_eq (H1 l)=>[[m1[|]]|]e1//.
      case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//.
      case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//. by subst. }
    { case_eq (H1 l)=>[[m1[|]]|]e1//.
      case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//.
      by case_eq (H2 l)=>[[m2[|]]|]e2[e3 e4]//. } }
  { move=>l.
    have:=wr l. have:=mrg l.
    case_eq (H l)=>[[m[|]]|]e.
    { case_eq (H2 l)=>[[m1[|]]|]e1//.
      case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//. by subst.
      by case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//. }
    { case_eq (H2 l)=>[[m1[|]]|]e1//.
      case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//.
      case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//. by subst. }
    { case_eq (H2 l)=>[[m1[|]]|]e1//.
      case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//.
      by case_eq (H1 l)=>[[m2[|]]|]e2[e3 e4]//. } }
Qed.

Lemma free_wr H H' l m : free H l m H' -> wr_heap H -> wr_heap H'.
Proof with eauto.
  move=>fr wr x. move: fr (wr x). rewrite/free.
  case_eq (H l)=>[[n[e[e1 e2]|e[e1 e2]]]|]//; subst=>//.
  rewrite remmE. by case_eq (x == l)=>/eqP e0.
Qed.

Lemma nf_weaken i j m : nf i m -> i <= j -> nf j m.
Proof with eauto using nf.
  move=>nfm. elim: nfm j=>{m i}...
  move=>i x lt1 j lt2.
  constructor.
  apply: leq_trans...
Qed.

Lemma resolve_wr_box H m : wr_heap H -> ~H ; m ~ Box.
Proof with eauto.
  move e:(Box)=>n wr rs. elim: rs wr e=>//{H m n}.
  move=>H H' l m m' fr rs ih wr e; subst.
  apply: ih...
  apply: free_wr...
Qed.

Lemma resolve_wr_nfi H m m' i :
  H ; m ~ m' -> wr_heap H -> nf i m' -> nf i m.
Proof with eauto using nf.
  move=>rs. elim: rs i=>{H m m'}...
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' rsm ihm i wr nfA. inv nfA... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfA. inv nfA...
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      exfalso. apply: resolve_wr_box... }
    { have[wr1 wr2]:=wr_merge_inv mrg wr... } }
  { move=>H m m' t rsm ihm i wr nfP. inv nfP... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfL. inv nfL.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n1 n1' n2 n2'
           mrg erm ihm ern1 ihn1 ern2 ihn2 i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H m m' rsm ihm i wr nf. inv nf... }
Qed.

Lemma resolve_wr_nfi' H m m' i :
  H ; m ~ m' -> wr_heap H -> nf i m -> nf i m'.
Proof with eauto using nf.
  move=>rs. elim: rs i=>{H m m'}...
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' rsm ihm i wr nfA. inv nfA... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfA. inv nfA.
    { inv rsn. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr... } }
  { move=>H m m' t rsm ihm i wr nfP. inv nfP... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfL. inv nfL.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n1 n1' n2 n2'
           mrg erm ihm ern1 ihn1 ern2 ihn2 i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H m m' rsm ihm i wr nf. inv nf... }
  { move=>H H' l m m' fr rsm ihm i wr nfP.
    apply: ihm.
    { apply: free_wr... }
    { have nf0:=free_wr_nf fr wr.
      apply: nf_weaken... } }
Qed.

Lemma free_wr_ptr H H' l i :
  free H l (Ptr i) H' -> wr_heap H -> False.
Proof with eauto.
  move e:(Ptr i)=>m fr wr; subst.
  move: fr. rewrite/free.
  rmatch_case.
  have:=wr l. by rewrite H2.
  have:=wr l. by rewrite H2.
Qed.

Lemma free_wr_var H H' l x :
  free H l (Var x) H' -> wr_heap H -> False.
Proof with eauto.
  move e:(Var x)=>m fr wr; subst.
  move: fr. rewrite/free.
  rmatch_case.
  have:=wr l. by rewrite H2.
  have:=wr l. by rewrite H2.
Qed.

Lemma free_wr_lam0 H H' l A m :
  free H l (Lam0 A m U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Lam0 A m U)=>n fr wr; subst.
  move: fr. rewrite/free.
  rmatch_case.
  have:=wr l. rewrite H2.
  case A=>//. move=>[_ e]. by inv e.
Qed.

Lemma free_wr_lam1 H H' l A m :
  free H l (Lam1 A m U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Lam1 A m U)=>n fr wr; subst.
  move: fr. rewrite/free. rmatch_case.
  have:=wr l. rewrite H2. rmatch_case.
Qed.

Lemma free_wr_pair0 H H' l m n :
  free H l (Pair0 m n U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Pair0 m n U)=>x fr wr; subst.
  move: fr. rewrite/free. rmatch_case.
  have:=wr l. rewrite H2. rmatch_case.
Qed.

Lemma free_wr_pair1 H H' l m n :
  free H l (Pair1 m n U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Pair1 m n U)=>x fr wr; subst.
  move: fr. rewrite/free. rmatch_case.
  have:=wr l. rewrite H2. rmatch_case.
Qed.

Lemma free_wr_tt H H' l :
  free H l TT H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(TT)=>x fr wr; subst.
  move: fr. rewrite/free. rmatch_case.
  have:=wr l. rewrite H2. rmatch_case.
Qed.

Lemma free_wr_ff H H' l :
  free H l FF H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(FF)=>x fr wr; subst.
  move: fr. rewrite/free. rmatch_case.
  have:=wr l. rewrite H2. rmatch_case.
Qed.

Lemma resolve_var_inv H m x :
  wr_heap H -> H ; m ~ Var x -> H ▷ U.
Proof with eauto.
  move e:(Var x)=>n wr rs.
  elim: rs x e wr=>//{H m n}.
  move=>H H' l m m' fr rsm ih x e wr; subst.
  destruct m; inv rsm.
  exfalso. apply: free_wr_var...
  exfalso. apply: free_wr_ptr...
Qed.

Lemma resolve_lam0_inv H m A n s :
  wr_heap H -> H ; m ~ Lam0 A n s -> H ▷ s.
Proof with eauto using hkey_impure.
  move e:(Lam0 A n s)=>v wr rs.
  elim: rs A n s e wr=>//{H m v}.
  { move=>H m m' s k rsm ihm A n s0[e1 e2 e3]; subst... }
  { move=>H H' l m m' fr rsm ihm A n s e wr; subst.
    destruct m; inv rsm.
    { destruct s... have->//:=free_wr_lam0 fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Lemma resolve_lam1_inv H m A n s :
  wr_heap H -> H ; m ~ Lam1 A n s -> H ▷ s.
Proof with eauto using hkey_impure.
  move e:(Lam1 A n s)=>v wr rs.
  elim: rs A n s e wr=>//{H m v}.
  { move=>H m m' s k rsm ihm A n s0[e1 e2 e3]; subst... }
  { move=>H H' l m m' fr rsm ihm A n s e wr; subst.
    destruct m; inv rsm.
    { destruct s... have->//:=free_wr_lam1 fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Lemma resolve_tt_inv H m :
  wr_heap H -> H ; m ~ TT -> H ▷ U.
Proof with eauto using hkey_impure.
  move e:(TT)=>v wr rs.
  elim: rs e wr=>//{H m v}.
  { move=>H H' l m m' fr rsm ihm e wr; subst.
    destruct m; inv rsm.
    { have->//:=free_wr_tt fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Lemma resolve_ff_inv H m :
  wr_heap H -> H ; m ~ FF -> H ▷ U.
Proof with eauto using hkey_impure.
  move e:(FF)=>v wr rs.
  elim: rs e wr=>//{H m v}.
  { move=>H H' l m m' fr rsm ihm e wr; subst.
    destruct m; inv rsm.
    { have->//:=free_wr_ff fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Theorem resolution H x y z A s l :
  H ; x ~ y ~ z : A ->
  nil ⊢ A : Sort s l ->
  dyn_val y -> wr_heap H -> H ▷ s.
Proof with eauto using hkey_impure.
  move=>wr. inv wr.
  move:H1 H2.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty H z s l e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H z s0 l e1 e2 rs tyA vl wr; subst. inv shs. }
  { move=>Γ Δ A B m m' s k erm _ H z s0 l e1 e2 rs tyP vl wr; subst.
    have[t[l1[l2[tyB/sort_inj[e1 e2]]]]]:=sta_pi0_inv tyP. subst.
    destruct s...
    apply: resolve_lam0_inv... }
  { move=>Γ Δ A B m m' s t k erm _ H z s0 l e1 e2 rs tyP vl wr; subst.
    have[r[l1[l2[tyB/sort_inj[e1 e2]]]]]:=sta_pi1_inv tyP. subst.
    destruct s...
    apply: resolve_lam1_inv... }
  { move=>Γ Δ A B m m' n s erm _ tyn
      H z s0 l e1 e2 rs tyB vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm _ ern _
      H z s0 l e1 e2 rs tyB vl. inv vl. }
  { move=>Γ Δ A B m m' n t l tyS1 erm ihm tyn
      H z s l0 e1 e2 rs tyS2 vl wr; subst.
    have[s0[r[l1[l2[ord[tyA[tyB/sort_inj[e1 e2]]]]]]]]:=sta_sig0_inv tyS2. subst.
    destruct t... inv ord. inv vl.
    inv rs... have wr':=free_wr H2 wr. inv H3.
    { have k':=ihm _ _ _ _ erefl erefl H7 tyA H1 wr'.
      have->//:=free_wr_pair0 H2 wr. }
    { exfalso. apply: free_wr_ptr... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t l mrg tyS1 erm ihm ern ihn
      H z s l0 e1 e2 rs tyS2 vl wr; subst.
    inv mrg. inv vl.
    have[s0[r[l1[l2[ord1[ord2[tyA[tyB/sort_inj[e1 e2]]]]]]]]]:=sta_sig1_inv tyS2. subst.
    destruct t... inv ord1. inv ord2.
    inv rs.
    { have[wr1 wr2]:=wr_merge_inv H10 wr.
      have tym:=dyn_sta_type (era_dyn_type erm).
      have tyBm:=sta_subst tyB tym. asimpl in tyBm.
      have k1:=ihm _ _ _ _ erefl erefl H11 tyA H2 wr1.
      have k2:=ihn _ _ _ _ erefl erefl H12 tyBm H4 wr2.
      apply: hmrg_pure... }
    { have wr':=free_wr H1 wr. inv H3.
      { have[wr1 wr2]:=wr_merge_inv H12 wr'.
        have tym:=dyn_sta_type (era_dyn_type erm).
        have tyBm:=sta_subst tyB tym. asimpl in tyBm.
        have k1:=ihm _ _ _ _ erefl erefl H13 tyA H2 wr1.
        have k2:=ihn _ _ _ _ erefl erefl H14 tyBm H4 wr2.
        have->:=free_wr_pair1 H1 wr.
        apply: hmrg_pure... }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t l mrg tyC1 erm _ ern _
      H z s0 l0 e1 e2 rs tyC2 vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s l r1 r2 t mrg tyC1 erm _ ern _
      H z s0 l0 e1 e2 rs tyC2 vl. inv vl. }
  { move=>Γ Δ wf k H z s l e1 e2 rs tyB1 vl wr. subst.
    have tyB2:=sta_bool sta_wf_nil.
    have e:=sta_unicity tyB1 tyB2. subst.
    have//:=resolve_tt_inv wr rs. }
  { move=>Γ Δ wf k H z s l e1 e2 rs tyB1 vl wr. subst.
    have tyB2:=sta_bool sta_wf_nil.
    have e:=sta_unicity tyB1 tyB2. subst.
    have//:=resolve_ff_inv wr rs. }
  { move=>Γ Δ1 Δ2 Δ A m m' n1 n1' n2 n2' s l mrg tyA erm ihm ern1 ihn1 ern2 ihn2
           H z s0 l0 e1 e2 rs tyAm vl. inv vl. }
  { move=>Γ Δ A B x x' P m n s l tyB erH _ tyP H z s0 l0 e1 e2 rs tyB' vl. inv vl. }
  { move=>Γ Δ A B m m' s l eq erm ihm tyB1 H z s0 l0 e1 e2 rs tyB2 vl wr.
    have e:=sta_unicity tyB1 tyB2. subst.
    have[s[lA tyA]]:=dyn_valid (era_dyn_type erm).
    have[x r1 r2]:=church_rosser eq.
    have tyx1:=sta_rd tyA r1.
    have tyx2:=sta_rd tyB1 r2.
    have e:=sta_unicity tyx1 tyx2. subst... }
Qed.

Lemma wr_free_dyn_val H l m H' :
  free H l m H' -> wr_heap H -> dyn_val m.
Proof with eauto using dyn_val.
  move=>fr wr. move: fr (wr l). rewrite/free.
  rmatch_case...
Qed.

Lemma resolve_dyn_val H m n :
  H ; m ~ n -> dyn_val m -> wr_heap H -> dyn_val n.
Proof with eauto using dyn_val.
  move=>rsm. elim: rsm=>{H m n}...
  { move=>H m m' rsm _ vl. inv vl. }
  { move=>H1 H2 H m m' n n' mrg rsm _ rsn _ vl. inv vl. }
  { move=>H m m' t rsm ihm vl wr. inv vl... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn vl wr.
    have[wr1 wr2]:=wr_merge_inv mrg wr. inv vl... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn vl. inv vl. }
  { move=>H1 H2 H m m' n1 n1' n2 n2' mrg erm ihm ern1 ihn1 ern2 ihn2 vl. inv vl. }
  { move=>H m m' rsm ihm vl. inv vl. }
  { move=>H H' l m m' fr rsm ihm _ wr.
    have wr':=free_wr fr wr.
    have vl:=wr_free_dyn_val fr wr... }
Qed.

Lemma wr_resolve_ptr H l n :
  wr_heap H -> H ; Ptr l ~ n -> dyn_val n.
Proof with eauto.
  move=>wr rs. inv rs.
  have wr':=free_wr H2 wr.
  have vl:=wr_free_dyn_val H2 wr.
  apply: resolve_dyn_val...
Qed.
