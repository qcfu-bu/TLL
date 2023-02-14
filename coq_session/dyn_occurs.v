From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq zify.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_conf sta_uniq dyn_type dyn_cren dyn_valid dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive cvar_pos : dyn_ctx -> cvar -> bool -> Prop :=
| cvar_pos_nil i :
  cvar_pos nil i false
| cvar_pos_ty Θ A :
  cvar_pos (A :L Θ) 0 true
| cvar_pos_n Θ :
  cvar_pos (_: Θ) 0 false
| cvar_pos_cons Θ x A b :
  cvar_pos Θ x b ->
  cvar_pos (A :: Θ) x.+1 b.

Fixpoint dyn_occurs (i : cvar) (m : term) : nat :=
  match m with
  | Var _ => 0
  | Sort _ => 0
  | Pi0 _ _ _ => 0
  | Pi1 _ _ _ => 0
  | Lam0 _ m _ => dyn_occurs i m
  | Lam1 _ m _ => dyn_occurs i m
  | App0 m _ => dyn_occurs i m
  | App1 m n => dyn_occurs i m + dyn_occurs i n
  | Sig0 _ _ _ => 0
  | Sig1 _ _ _ => 0
  | Pair0 _ n _ => dyn_occurs i n
  | Pair1 m n _ => dyn_occurs i m + dyn_occurs i n
  | LetIn _ m n => dyn_occurs i m + dyn_occurs i n
  | Fix _ m => dyn_occurs i m
  | Unit => 0
  | Bool => 0
  | II => 0
  | TT => 0
  | FF => 0
  | Ifte _ m n1 n2  => dyn_occurs i m + maxn (dyn_occurs i n1) (dyn_occurs i n2)
  | IO _ => 0
  | Return m => dyn_occurs i m
  | Bind m n => dyn_occurs i m + dyn_occurs i n
  | Proto => 0
  | Stop _ => 0
  | Act0 _ _ _ => 0
  | Act1 _ _ _ => 0
  | Ch _ _ => 0
  | CVar x => if x == i then 1 else 0
  | Fork _ m => dyn_occurs i m
  | Recv0 m => dyn_occurs i m
  | Recv1 m => dyn_occurs i m
  | Send0 m => dyn_occurs i m
  | Send1 m => dyn_occurs i m
  | Close m => dyn_occurs i m
  | Wait m => dyn_occurs i m
  end.

Lemma cvar_pos_merge_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> 
  cvar_pos Θ1 i false ->
  cvar_pos Θ2 i false ->
  cvar_pos Θ i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1. inv pos2... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos1 pos2. inv pos1; inv pos2... }
  { move=>Θ1 Θ2 Θ mrg ih i pos1 pos2. inv pos1; inv pos2... }
Qed.

Lemma cvar_pos_split_false Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i false ->
  cvar_pos Θ1 i false /\
  cvar_pos Θ2 i false.
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}...
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[pos1 pos2]:=ih _ H3... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos...
    have[pos1 pos2]:=ih _ H3... }
Qed.

Lemma cvar_pos_split_true Θ1 Θ2 Θ i :
  Θ1 ∘ Θ2 => Θ -> cvar_pos Θ i true ->
  (cvar_pos Θ1 i false /\ cvar_pos Θ2 i true) \/
  (cvar_pos Θ1 i true /\ cvar_pos Θ2 i false).
Proof with eauto using cvar_pos.
  move=>mrg. elim: mrg i=>{Θ1 Θ2 Θ}.
  { move=>i pos. inv pos. }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    right...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ m mrg ih i pos. inv pos.
    left...
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
  { move=>Θ1 Θ2 Θ mrg ih i pos. inv pos.
    have[[pos1 pos2]|[pos1 pos2]]:=ih _ H3.
    left... right... }
Qed.

Lemma dyn_empty_pos_true Θ i : dyn_empty Θ -> cvar_pos Θ i true -> False.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i pos. inv pos. }
  { move=>Δ emp ih i pos. inv pos.
    apply: ih. apply: H3. }
Qed.

Lemma dyn_empty_pos_false Θ i : dyn_empty Θ -> cvar_pos Θ i false.
Proof.
  move=>emp. elim: emp i=>{Θ}.
  { move=>i. constructor. }
  { move=>Δ emp ih[|i].
    constructor.
    by constructor. }
Qed.

Lemma dyn_just_pos_true Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i true <-> x == i = true.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos=>//.
      exfalso. apply: dyn_empty_pos_true... }
    { move=>/eqP<-. constructor. } }
  { move=>Δ A x js ih i. split.
    { move=>pos. inv pos. move/ih in H3... }
    { move=>/eqP<-. constructor.
      rewrite ih. by apply/eqP. } }
Qed.

Lemma dyn_just_pos_false Θ x i A :
  dyn_just Θ x A -> cvar_pos Θ i false <-> x == i = false.
Proof with eauto.
  move=>js. elim: js i=>{Θ x A}.
  { move=>Δ A emp i. split.
    { move=>pos. inv pos. by apply/eqP. }
    { move: i=>[|i]/eqP//_.
      constructor. by apply: dyn_empty_pos_false. } }
  { move=>Δ A x js ih i. split. 
    { move=>pos. inv pos.
      by apply/eqP.
      move/ih in H3... }
    { move: i=>[|i] neq...
      constructor.
      constructor.
      rewrite ih... } }
Qed.

Lemma dyn_type_occurs0 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i false -> dyn_occurs i m = 0.
Proof with eauto using dyn_occurs.
  move=>ty. elim: ty i=>//={Θ Γ Δ m A}...
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
            tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->:=ihn1 _ pos2.
    have->//:=ihn2 _ pos2. }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[pos1 pos2]:=cvar_pos_split_false mrg1 pos.
    have->:=ihm _ pos1.
    have->//:=ihn _ pos2. }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    move/(dyn_just_pos_false _ js) in pos.
    rewrite pos... }
Qed.

Lemma dyn_type_occurs1 Θ Γ Δ m A i :
  Θ ; Γ ; Δ ⊢ m : A -> cvar_pos Θ i true -> dyn_occurs i m = 1.
Proof with eauto using dyn_occurs, dyn_type_occurs0.
  move=>ty. elim: ty i=>//={Θ Γ Δ m A}...
  { move=>Θ Γ Δ x s A emp wf shs dhs i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { rewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
            tyS tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
            tyC tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ Γ Δ emp wf k i pos.
    exfalso. apply: dyn_empty_pos_true... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn1...
      erewrite ihn2...
      erewrite dyn_type_occurs0... }
    { erewrite ihm...
      erewrite dyn_type_occurs0...
      erewrite dyn_type_occurs0... } }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn i pos.
    have[[pos1 pos2]|[pos1 pos2]]:=cvar_pos_split_true mrg1 pos.
    { erewrite ihn...
      erewrite dyn_type_occurs0... }
    { erewrite ihm... } }
  { move=>Θ Γ Δ r x A js wf k tyA i pos.
    move/(dyn_just_pos_true _ js) in pos.
    rewrite pos... }
Qed.

Definition iren i (ξ : cvar -> cvar) := forall x, ξ x == i = false.

Lemma iren0 : iren 0 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren1 : iren 1 (+2).
Proof. elim; simpl; eauto. Qed.

Lemma iren_upren i ξ : iren i ξ -> iren i.+1 (upren ξ).
Proof.
  move=> ir x.
  elim: x.
  asimpl; eauto.
  asimpl=>n e; eauto.
Qed.

Lemma dyn_occurs_iren Θ Γ Δ m A i ξ :
  Θ ; Γ ; Δ ⊢ term_cren m ξ : A -> iren i ξ -> dyn_occurs i (term_cren m ξ) = 0.
Proof with eauto using dyn_occurs.
  move e:(term_cren m ξ)=>x ty.
  elim: ty m ξ e i=>//={Θ Γ Δ x A}...
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2
           tyS tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2
           tyC tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2
           tyA tym ihm tyn1 ihn1 tyn2 ihn2 m0 ξ e i h.
    destruct m0; inv e.
    erewrite ihm... erewrite ihn1... erewrite ihn2... }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2
           tyB tym ihm tyn ihn m0 ξ e i h.
    destruct m0; inv e. erewrite ihm... }
  { move=>Θ Γ Δ r x A js wf k tyA m ξ e i h.
    destruct m; inv e.
    by rewrite h. }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 A B m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
  { move=>Θ Γ Δ r1 r2 m xor tym ihm m0 ξ e i h.
    destruct m0; inv e... }
Qed.

Lemma dyn_occurs_cren_id Θ Γ Δ m A i j ξ :
  Θ ; Γ ; Δ ⊢ term_cren m ξ : A ->
  dyn_occurs i m = 0 ->
  dyn_occurs j m = 0 ->
  (forall x, x == i = false -> x == j = false -> ξ x = x) ->
  Θ ; Γ ; Δ ⊢ m : A.
Proof with eauto using dyn_type.
  move e:(term_cren m ξ)=>m' ty.
  elim: ty m ξ e i j=>{Θ Γ Δ m' A}.
  all: try solve[intros;
                 match goal with
                 | [ H : term_cren ?m _ = _ |- _ ] =>
                     destruct m; inv H; eauto using dyn_type
                 end].
  { move=>Θ Γ Δ A B m s k1 k2 tym ihm m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have[r tyB]:=dyn_valid tym.
    have wf:=sta_type_wf tyB. inv wf.
    apply: dyn_conv.
    apply: sta_conv_pi0.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor...
    apply: dyn_ctx_conv0.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_crename_inv...
    apply: ihm.
    eauto.
    apply: oc1.
    apply: oc2.
    apply: h.
    econstructor... }
  { move=>Θ Γ Δ A B m s t k1 k2 tym ihm m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have[r tyB]:=dyn_valid tym.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_conv.
    apply: sta_conv_pi1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    eauto.
    econstructor...
    apply: dyn_ctx_conv1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_crename_inv...
    apply: ihm.
    eauto.
    apply: oc1.
    apply: oc2.
    apply: h.
    econstructor... }
  { move=>Θ Γ Δ A B m n s tym ihm tyn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have[r tyP]:=dyn_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi0_inv tyP. subst.
    apply: dyn_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    apply: sta_crename_inv...
    have:=sta_subst tyB tyn... }
  { move=>Θ1 Θ2 θ Γ Δ1 Δ2 Δ A B m n s mrg1 mrg2 tym ihm tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have[r tyP]:=dyn_valid tym.
    have[t[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
    move:oc1. case_eq (dyn_occurs i m0_1); case_eq (dyn_occurs i m0_2)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m0_1); case_eq (dyn_occurs j m0_2)=>//e3 e4 _.
    apply: dyn_conv.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor...
    have:=sta_subst tyB (dyn_sta_type tyn)... }
  { move=>Θ Γ Δ A B m n t tyS tym tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    econstructor...
    apply: sta_crename_inv...
    apply: dyn_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: ihn.
    eauto.
    apply: oc1.
    apply: oc2.
    eauto.
    have/=:=sta_subst tyB (sta_crename_inv tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrg1 mrg2 tyS tym ihm tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    move:oc1. case_eq (dyn_occurs i m0_1); case_eq (dyn_occurs i m0_2)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m0_1); case_eq (dyn_occurs j m0_2)=>//e3 e4 _.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
    econstructor...
    apply: dyn_conv.
    apply: sta_conv_beta.
    apply: sta_cren_conv0...
    apply: ihn.
    eauto.
    apply: e1.
    apply: e3.
    eauto.
    have/=:=sta_subst tyB (sta_crename_inv (dyn_sta_type tym))... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrg1 mrg2 tyC tym ihm tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    move:oc1. case_eq (dyn_occurs i m0); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m0); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    have tyA0:=sta_crename_inv tyC.
    have wf:=sta_type_wf tyA0. inv wf.
    have[s1[r1[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2. subst.
    have agr:sta_agree_subst (B :: A :: Γ) (Pair0 (Var 1) (Var 0) t .: ren (+2)) (Sig0 A B t :: Γ).
    { econstructor.
      replace (ren (+2)) with (ids >> (ren (+1)) >> (ren (+1))) by autosubst.
      econstructor...
      econstructor...
      asimpl.
      econstructor.
      replace (Sig0 A.[ren (+2)] B.[ren (0 .: (+3))] t)
        with (Sig0 A B t).[ren (+2)] by autosubst.
      replace (Sort t) with (Sort t).[ren (+2)] by eauto.
      apply: sta_rename...
      replace (+2) with ((+1) >>> (+1) >>> id) by autosubst.
      econstructor...
      econstructor...
      apply: sta_agree_ren_refl...
      repeat constructor...
      replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
      repeat constructor.
      asimpl.
      repeat constructor... }
    have eq: A0.[m0/] === (term_cren A0 ξ).[term_cren m0 ξ/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    econstructor...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: ihn.
    eauto.
    apply: e1.
    apply: e3.
    eauto.
    have/=:=sta_substitution tyA0 agr...
    have/=:=sta_subst tyC (dyn_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg1 mrg2 tyC tym ihm tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    move:oc1. case_eq (dyn_occurs i m0); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m0); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    have tyA0:=sta_crename_inv tyC.
    have wf:=sta_type_wf tyA0. inv wf.
    have[s1[t1[ord1[ord[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2. subst.
    have agr:sta_agree_subst (B :: A :: Γ) (Pair1 (Var 1) (Var 0) t .: ren (+2)) (Sig1 A B t :: Γ).
    { econstructor.
      replace (ren (+2)) with (ids >> (ren (+1)) >> (ren (+1))) by autosubst.
      econstructor...
      econstructor...
      asimpl.
      econstructor.
      replace (Sig1 A.[ren (+2)] B.[ren (0 .: (+3))] t)
        with (Sig1 A B t).[ren (+2)] by autosubst.
      replace (Sort t) with (Sort t).[ren (+2)] by eauto.
      apply: sta_rename...
      replace (+2) with ((+1) >>> (+1) >>> id) by autosubst.
      econstructor...
      econstructor...
      apply: sta_agree_ren_refl...
      repeat constructor...
      replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
      repeat constructor.
      asimpl.
      repeat constructor... }
    have eq: A0.[m0/] === (term_cren A0 ξ).[term_cren m0 ξ/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    apply: dyn_letin1...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: ihn.
    eauto.
    apply: e1.
    apply: e3.
    eauto.
    have/=:=sta_substitution tyA0 agr...
    have/=:=sta_subst tyC (dyn_sta_type tym)... }
  { move=>Θ Γ Δ A m k1 k2 tym ihm m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have{}ihm:=ihm _ _ erefl _ _ oc1 oc2 h.
    have wf:=dyn_type_wf ihm. inv wf.
    apply: dyn_conv.
    apply: conv_sym.
    apply: sta_cren_conv0...
    2:{ eauto. }
    econstructor...
    apply: dyn_ctx_conv1.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_crename_inv...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    apply: ihm.
    have/=:=sta_weaken (sta_crename_inv H4) H4... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrg1 mrg2 tyA
           tym ihm tyn1 ihn1 tyn2 ihn2 m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have wf:=sta_type_wf tyA. inv wf.
    move:oc1.
    case_eq (dyn_occurs i m0_1);
      case_eq (dyn_occurs i m0_2);
      case_eq (dyn_occurs i m0_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e11 e12 e13 _.
    move:oc2.
    case_eq (dyn_occurs j m0_1);
      case_eq (dyn_occurs j m0_2);
      case_eq (dyn_occurs j m0_3)=>//=.
    2:{ move=>n1 e1 n2 e2 e3 e4.
        rewrite maxnSS in e4. inv e4. }
    move=>e21 e22 e23 _.
    have{}ihm:=ihm _ _ erefl _ _ e13 e23 h.
    have{}ihn1:=ihn1 _ _ erefl _ _ e12 e22 h.
    have{}ihn2:=ihn2 _ _ erefl _ _ e11 e21 h.
    have eq: A0.[m0_1/] === (term_cren A0 ξ).[term_cren m0_1 ξ/].
    apply: conv_trans.
    apply: sta_conv_beta.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: sta_conv_subst.
    apply: conv_sym.
    apply: sta_cren_conv0...
    apply: dyn_conv...
    econstructor...
    apply: sta_crename_inv...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    have/=:=sta_subst (sta_crename_inv tyA) (sta_tt H1)...
    apply: dyn_conv.
    apply: sta_conv_subst.
    apply: sta_cren_conv0...
    eauto.
    have/=:=sta_subst (sta_crename_inv tyA) (sta_ff H1)...
    have/=:=sta_subst tyA (dyn_sta_type tym)... }
  { move=>Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrg1 mrg2 tyB tym ihm tyn ihn m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    move:oc1. case_eq (dyn_occurs i m0); case_eq (dyn_occurs i n0)=>//e1 e2 _.
    move:oc2. case_eq (dyn_occurs j m0); case_eq (dyn_occurs j n0)=>//e3 e4 _.
    have{}ihm:=ihm _ _ erefl _ _ e2 e4 h.
    have{}ihn:=ihn _ _ erefl _ _ e1 e3 h.
    econstructor... }
  { move=>Θ Γ Δ r x A js wf k tyA m ξ e i j oc1 oc2 h.
    destruct m; inv e.
    move: oc1 oc2=>/=.
    case_eq (x0 == i); case_eq (x0 == j)=>// e1 e2 _ _.
    constructor...
    rewrite h in js... }
  { move=>Θ Γ Δ m A tym ihm m0 ξ e i j oc1 oc2 h.
    destruct m0; inv e. simpl in oc1. simpl in oc2.
    have{}ihm:=ihm _ _ erefl _ _ oc1 oc2 h.
    have wf:=dyn_type_wf ihm. inv wf.
    have[tym0 _]:=sta_ch_inv H4.
    apply: dyn_conv.
    3:{ econstructor.
        constructor... }
    apply: sta_conv_io.
    apply: sta_conv_ch.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor.
    apply: dyn_ctx_conv1.
    3:{ apply: ihm. }
    apply: sta_conv_ch.
    apply: conv_sym.
    apply: sta_cren_conv0...
    econstructor.
    apply: sta_crename_inv... }
Qed.
