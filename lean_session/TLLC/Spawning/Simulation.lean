import TLLC.Process.Step
import TLLC.Spawning.Flatten
import TLLC.Spawning.Step

/-!
# Spawning-tree simulation

Lemma 5.86 for the productive spawning-tree step relation. Finished-subtree cleanup is not part of
`Step`; terminality and process structural congruence handle it separately.
-/

namespace TLLC.Spawning
open Autosubst Autosubst.Notation
open TLLC.Dynamic

lemma SubtreesTyped.typed_of_mem {trees : List Tree} {tree : Tree}
    (typed : SubtreesTyped trees) (member : tree ∈ trees) :
    Typed tree := by
  induction trees generalizing tree with
  | nil =>
      cases member
  | cons _ _ ih =>
      cases typed with
      | cons typedHead typedTail =>
          cases member with
          | head =>
              exact typedHead
          | tail _ memberTail =>
              exact ih typedTail memberTail

lemma Typed.subtree_typed {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {subtree : Tree}
    (typed : Typed (.root m children subtrees)) (member : subtree ∈ subtrees) :
    Typed subtree := by
  cases typed with
  | root _ _ _ typedSubtrees =>
      exact typedSubtrees.typed_of_mem member

lemma TypedAt.subtree_typed {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {subtree : Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node parent m children subtrees)) (member : subtree ∈ subtrees) :
    Typed subtree := by
  cases typed with
  | node _ _ _ _ typedSubtrees =>
      exact typedSubtrees.typed_of_mem member

lemma shiftChildren_mem_child {children : List (Chan × Tree)} {c : Chan} {child : Tree}
    (member : (c, child) ∈ shiftChildren children) :
    ∃ c', (c', child) ∈ children := by
  induction children with
  | nil =>
      cases member
  | cons edge children ih =>
      rcases edge with ⟨edgeChannel, edgeChild⟩
      cases edgeChannel with
      | var_Chan edgeIndex =>
          cases member with
          | head =>
              exact ⟨.var_Chan edgeIndex, by simp⟩
          | tail _ tail =>
              obtain ⟨c', memberTail⟩ := ih tail
              exact ⟨c', by simp [memberTail]⟩

lemma ChildrenTyped.typedAt_of_mem {Θ : PCtx} {children : List (Chan × Tree)}
    {c : Chan} {child : Tree}
    (typed : ChildrenTyped Θ children) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  induction Θ generalizing children c child with
  | nil =>
      cases typed
      cases member
  | cons _ Θ ih =>
      cases typed with
      | none typedTail =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact ih typedTail memberTail
      | one typedChild typedTail =>
          cases member with
          | head =>
              exact ⟨_, _, typedChild⟩
          | tail _ memberTail =>
              obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
              exact ih typedTail memberTailOriginal

lemma ChildrenTypedAt.typedAt_of_mem {Θ : PCtx} {x : Nat} {role : Bool} {protocol : Term}
    {children : List (Chan × Tree)} {c : Chan} {child : Tree}
    (typed : ChildrenTypedAt Θ x role protocol children) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  induction Θ generalizing x protocol children c child with
  | nil =>
      cases typed
  | cons _ Θ ih =>
      cases typed with
      | parent typedChildren =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact typedChildren.typedAt_of_mem memberTail
      | none typedTail =>
          obtain ⟨c', memberTail⟩ := shiftChildren_mem_child member
          exact ih typedTail memberTail
      | one typedChild typedTail =>
          cases member with
          | head =>
              exact ⟨_, _, typedChild⟩
          | tail _ memberTail =>
              obtain ⟨c', memberTailOriginal⟩ := shiftChildren_mem_child memberTail
              exact ih typedTail memberTailOriginal

lemma Typed.child_typedAt {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree}
    (typed : Typed (.root m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  cases typed with
  | root _ _ typedChildren _ =>
      exact typedChildren.typedAt_of_mem member

lemma TypedAt.child_typedAt {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {c : Chan} {child : Tree} {r : Bool} {A : Term}
    (typed : TypedAt r A (.node parent m children subtrees)) (member : (c, child) ∈ children) :
    ∃ r A, TypedAt r A child := by
  cases typed with
  | node _ _ _ typedChildren _ =>
      exact typedChildren.typedAt_of_mem member

lemma Step.node_result {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {tree : Tree}
    (step : Step (.node parent m children subtrees) tree) :
    ∃ m' children' subtrees', tree = .node parent m' children' subtrees' := by
  cases step <;> repeat first | exact ⟨_, _, _, rfl⟩

lemma Step.node_flattenAt_eq {parent : Chan} {m : Term} {children : List (Chan × Tree)}
    {subtrees : List Tree} {tree : Tree}
    (step : Step (.node parent m children subtrees) tree) :
    tree.flattenAt = (parent, tree.flatten) := by
  obtain ⟨m', children', subtrees', rfl⟩ := step.node_result
  simp

lemma dynamic_thunk_csubst {m : Term} (thunk : Thunk m) :
    ∀ σ : Nat → Chan, Thunk (m[σ; Term.var_Term]) := by
  induction thunk using @TLLC.Dynamic.Thunk.rec
    (motive_2 := fun m _ => ∀ σ : Nat → Chan, Val (m[σ; Term.var_Term])) with
  | mlet thunk ih =>
      intro σ
      simpa using Thunk.mlet (ih σ)
  | fork =>
      intro σ
      simpa using (Thunk.fork (A := _))
  | recv =>
      intro σ
      simpa using (Thunk.recv (c := _))
  | appSendIm =>
      intro σ
      simpa using (Thunk.appSendIm (c := _))
  | appSendEx value ih =>
      intro σ
      simpa using Thunk.appSendEx (ih σ)
  | close =>
      intro σ
      simpa using (Thunk.close (c := _))
  | var =>
      simpa using (Val.var (x := _))
  | lam =>
      simpa using (Val.lam (A := _))
  | pairIm value ih =>
      simpa using Val.pairIm (ih _)
  | pairEx valueLeft valueRight ihLeft ihRight =>
      simpa using Val.pairEx (ihLeft _) (ihRight _)
  | one =>
      simpa using Val.one
  | tt =>
      simpa using Val.tt
  | ff =>
      simpa using Val.ff
  | pure value ih =>
      simpa using Val.pure (ih _)
  | chan =>
      simpa using (Val.chan (x := _))
  | send =>
      simpa using (Val.send (c := _))
  | thunk thunk ih =>
      simpa using Val.thunk (ih _)

lemma dynamic_val_csubst {m : Term} (value : Val m) :
    ∀ σ : Nat → Chan, Val (m[σ; Term.var_Term]) := by
  induction value using @TLLC.Dynamic.Val.rec
    (motive_1 := fun m _ => ∀ σ : Nat → Chan, Thunk (m[σ; Term.var_Term])) with
  | mlet thunk ih =>
      simpa using Thunk.mlet (ih _)
  | fork =>
      simpa using (Thunk.fork (A := _))
  | recv =>
      simpa using (Thunk.recv (c := _))
  | appSendIm =>
      simpa using (Thunk.appSendIm (c := _))
  | appSendEx value ih =>
      simpa using Thunk.appSendEx (ih _)
  | close =>
      simpa using (Thunk.close (c := _))
  | var =>
      intro σ
      simpa using (Val.var (x := _))
  | lam =>
      intro σ
      simpa using (Val.lam (A := _))
  | pairIm value ih =>
      intro σ
      simpa using Val.pairIm (ih σ)
  | pairEx valueLeft valueRight ihLeft ihRight =>
      intro σ
      simpa using Val.pairEx (ihLeft σ) (ihRight σ)
  | one =>
      intro σ
      simpa using Val.one
  | tt =>
      intro σ
      simpa using Val.tt
  | ff =>
      intro σ
      simpa using Val.ff
  | pure value ih =>
      intro σ
      simpa using Val.pure (ih σ)
  | chan =>
      intro σ
      simpa using (Val.chan (x := _))
  | send =>
      intro σ
      simpa using (Val.send (c := _))
  | thunk thunk ih =>
      intro σ
      simpa using Val.thunk (ih σ)

lemma dynamic_step_csubst {m n : Term} (step : TLLC.Dynamic.Step m n) :
    ∀ σ : Nat → Chan,
      TLLC.Dynamic.Step (m[σ; Term.var_Term]) (n[σ; Term.var_Term]) := by
  induction step with
  | appL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.appL (ih σ)
  | appR step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.appR (ih σ)
  | betaIm =>
      rename_i A m n s
      intro σ
      convert
        (TLLC.Dynamic.Step.betaIm (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]) (n := n[σ; Term.var_Term]) (s := s))
        using 1 <;> asimp
  | betaEx value =>
      rename_i A m v s
      intro σ
      convert
        (TLLC.Dynamic.Step.betaEx (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]) (v := v[σ; Term.var_Term]) (s := s)
          (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | pairL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pairL (ih σ)
  | pairR step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pairR (ih σ)
  | projM step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.projM (ih σ)
  | projE value =>
      rename_i A m1 m2 n i s
      intro σ
      convert
        (TLLC.Dynamic.Step.projE (A := A[σ; Term.var_Term])
          (m1 := m1[σ; Term.var_Term]) (m2 := m2[σ; Term.var_Term])
          (n := n[σ; Term.var_Term]) (i := i) (s := s)
          (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | fixE =>
      rename_i A m
      intro σ
      convert
        (TLLC.Dynamic.Step.fixE (A := A[σ; Term.var_Term])
          (m := m[σ; Term.var_Term]))
        using 1 <;> asimp
  | iteM step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.iteM (ih σ)
  | iteT =>
      intro σ
      simpa using (TLLC.Dynamic.Step.iteT (A := _) (n1 := _) (n2 := _))
  | iteF =>
      intro σ
      simpa using (TLLC.Dynamic.Step.iteF (A := _) (n1 := _) (n2 := _))
  | pure step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.pure (ih σ)
  | mletL step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.mletL (ih σ)
  | mletE value =>
      rename_i v n
      intro σ
      convert
        (TLLC.Dynamic.Step.mletE (v := v[σ; Term.var_Term])
          (n := n[σ; Term.var_Term]) (dynamic_val_csubst value σ))
        using 1 <;> asimp
  | recv step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.recv (ih σ)
  | send step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.send (ih σ)
  | close step ih =>
      intro σ
      simpa using TLLC.Dynamic.Step.close (ih σ)

lemma evalctx_cren_comp (M : EvalCtx) (ξ ζ : Nat → Nat) :
    (M.cren ξ).cren ζ = M.cren (funcomp ζ ξ) := by
  induction M with
  | hole =>
      rfl
  | bnd M n ih =>
      simp [EvalCtx.cren, ih]
      asimp

lemma evalctx_csubst (σ : Nat → Chan) (M : EvalCtx) (m : Term) :
    (M.eval m)[σ; Term.var_Term] =
      (M.cren (TLLC.Static.csubst_ren σ)).eval (m[σ; Term.var_Term]) := by
  rw [← TLLC.Static.csubst_cren]
  rw [evalctx_cren]
  rw [TLLC.Static.csubst_cren]

lemma bindEndpointAt_self_term {c : Chan} {σ : Nat → Chan} :
    (Term.chan c)[bindEndpointAt 0 c; Term.var_Term][up_Chan_Chan σ; Term.var_Term] =
      TLLC.Process.cvar 0 := by
  cases c with
  | var_Chan x =>
      asimp
      unfold bindEndpointAt chanIndex
      simp
      asimp

lemma dynamic_val_crename {m : Term} (value : Val m) :
    ∀ ξ : Nat → Nat, Val (m⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  have renamed := dynamic_val_csubst value (fun x => Chan.var_Chan (ξ x))
  convert renamed using 1
  rw [← TLLC.Static.csubst_cren]
  congr

lemma dynamic_step_crename {m n : Term} (step : TLLC.Dynamic.Step m n) :
    ∀ ξ : Nat → Nat,
      TLLC.Dynamic.Step (m⟨ξ; (id : Nat → Nat)⟩) (n⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  have renamed := dynamic_step_csubst step (fun x => Chan.var_Chan (ξ x))
  convert renamed using 1
  · rw [← TLLC.Static.csubst_cren]
    congr
  · rw [← TLLC.Static.csubst_cren]
    congr

lemma process_congr0_crename {p q : Proc} (congr : TLLC.Process.Congr p q) :
    ∀ ξ : Nat → Nat,
      TLLC.Process.Congr (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  induction congr with
  | par_sym =>
      intro ξ
      simpa using TLLC.Process.Congr.par_sym
  | assoc =>
      intro ξ
      simpa using TLLC.Process.Congr.assoc
  | scope =>
      rename_i p q
      intro ξ
      convert (TLLC.Process.Congr.scope
        (p := p⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)
        (q := q⟨ξ; (id : Nat → Nat)⟩)) using 1
      · asimp
        congr 3
  | exch =>
      rename_i p
      intro ξ
      convert (TLLC.Process.Congr.exch
        (p := p⟨upRen_Chan_Chan (upRen_Chan_Chan ξ); (id : Nat → Nat)⟩)) using 1
        ; asimp
      · congr 2
  | par congrLeft congrRight ihLeft ihRight =>
      intro ξ
      simpa using TLLC.Process.Congr.par (ihLeft ξ) (ihRight ξ)
  | res congr ih =>
      intro ξ
      simpa using TLLC.Process.Congr.res (ih (upRen_Chan_Chan ξ))
  | «end» =>
      intro ξ
      simpa using TLLC.Process.Congr.end

lemma process_congr_crename {p q : Proc} (congr : TLLC.Process.Cong p q) :
    ∀ ξ : Nat → Nat,
      TLLC.Process.Cong (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  intro ξ
  induction congr with
  | refl =>
      exact TLLC.ARS.Conv.refl
  | tail _ step ih =>
      exact TLLC.ARS.Conv.tail ih (process_congr0_crename step ξ)
  | taili _ step ih =>
      exact TLLC.ARS.Conv.taili ih (process_congr0_crename step ξ)

lemma process_congr0_parallel_left {p q r : Proc}
    (congr : TLLC.Process.Congr p q) :
    TLLC.Process.Cong (.par p r) (.par q r) := by
  exact ARS.conv_trans
    (ARS.conv1i (TLLC.Process.Congr.end (p := .par p r)))
    (ARS.conv_trans
      (ARS.conv1i (TLLC.Process.Congr.assoc (o := p) (p := r) (q := .tm (.pure .one))))
      (ARS.conv1 (TLLC.Process.Congr.par congr (TLLC.Process.Congr.end (p := r)))))

lemma process_congr_parallel_left {p q r : Proc}
    (congr : TLLC.Process.Cong p q) :
    TLLC.Process.Cong (.par p r) (.par q r) := by
  induction congr with
  | refl =>
      exact ARS.Conv.refl
  | tail _ step ih =>
      exact ARS.conv_trans ih (process_congr0_parallel_left (r := r) step)
  | taili _ step ih =>
      exact ARS.conv_trans ih (ARS.conv_sym (process_congr0_parallel_left (r := r) step))

lemma process_congr_parallel_right {p q r : Proc}
    (congr : TLLC.Process.Cong p q) :
    TLLC.Process.Cong (.par r p) (.par r q) := by
  exact ARS.conv_trans
    (ARS.conv1 TLLC.Process.Congr.par_sym)
    (ARS.conv_trans (process_congr_parallel_left (r := r) congr)
      (ARS.conv1 TLLC.Process.Congr.par_sym))

lemma process_congr0_res {p q : Proc}
    (congr : TLLC.Process.Congr p q) :
    TLLC.Process.Cong (.nu p) (.nu q) := by
  exact ARS.conv1 (TLLC.Process.Congr.res congr)

lemma process_congr_res {p q : Proc}
    (congr : TLLC.Process.Cong p q) :
    TLLC.Process.Cong (.nu p) (.nu q) := by
  induction congr with
  | refl =>
      exact ARS.Conv.refl
  | tail _ step ih =>
      exact ARS.conv_trans ih (process_congr0_res step)
  | taili _ step ih =>
      exact ARS.conv_trans ih (ARS.conv_sym (process_congr0_res step))

lemma process_step_crename_zero {p q : Proc} (step : TLLC.Process.Step p q) :
    ∀ ξ : Nat → Nat, ξ 0 = 0 →
      TLLC.Process.Step (p⟨ξ; (id : Nat → Nat)⟩) (q⟨ξ; (id : Nat → Nat)⟩) := by
  induction step with
  | exp step =>
      intro ξ _
      simpa using TLLC.Process.Step.exp (dynamic_step_crename step ξ)
  | fork eqTerm eqCtx =>
      rename_i A m m' N N'
      intro ξ _
      subst eqTerm
      subst eqCtx
      convert (TLLC.Process.Step.fork
        (A := A⟨ξ; (id : Nat → Nat)⟩)
        (m := m⟨ξ; (id : Nat → Nat)⟩)
        (m' := (m⟨ξ; (id : Nat → Nat)⟩)⟨((· + 1) : Nat → Nat);
          (id : Nat → Nat)⟩)
        (N := N.cren ξ)
        (N' := (N.cren ξ).cren ((· + 1) : Nat → Nat)) rfl rfl) using 1
      · asimp
        rw [evalctx_cren]
        asimp
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren_comp]
        rw [show funcomp (upRen_Chan_Chan ξ) ((· + 1) : Nat → Nat) =
            funcomp ((· + 1) : Nat → Nat) ξ from by funext x; rfl]
        rw [← evalctx_cren_comp]
        asimp
        congr 3
  | comIm =>
      rename_i M N m
      intro ξ _
      convert (TLLC.Process.Step.comIm
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (m := m⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)) using 1
      all_goals
        asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
  | comEx value =>
      rename_i M N v
      intro ξ _
      convert (TLLC.Process.Step.comEx
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (v := v⟨upRen_Chan_Chan ξ; (id : Nat → Nat)⟩)
        (dynamic_val_crename value (upRen_Chan_Chan ξ))) using 1
      all_goals
        asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
  | «end» eqM eqN =>
      rename_i M N M' N'
      intro ξ h0
      subst eqM
      subst eqN
      convert (TLLC.Process.Step.end
        (M := M.cren (upRen_Chan_Chan ξ))
        (N := N.cren (upRen_Chan_Chan ξ))
        (M' := (M.cren (upRen_Chan_Chan ξ)).cren ((· - 1) : Nat → Nat))
        (N' := (N.cren (upRen_Chan_Chan ξ)).cren ((· - 1) : Nat → Nat)) rfl rfl) using 1
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
      · asimp
        rw [evalctx_cren]
        rw [evalctx_cren]
        asimp
        rw [evalctx_cren_comp M ((· - 1) : Nat → Nat) ξ]
        rw [evalctx_cren_comp N ((· - 1) : Nat → Nat) ξ]
        rw [evalctx_cren_comp M (upRen_Chan_Chan ξ) ((· - 1) : Nat → Nat)]
        rw [evalctx_cren_comp N (upRen_Chan_Chan ξ) ((· - 1) : Nat → Nat)]
        rw [show funcomp ((· - 1) : Nat → Nat) (upRen_Chan_Chan ξ) =
            funcomp ξ ((· - 1) : Nat → Nat) from by
              funext x
              cases x with
              | zero =>
                  exact h0.symm
              | succ x =>
                  rfl]
  | par step ih =>
      intro ξ h0
      simpa using TLLC.Process.Step.par (ih ξ h0)
  | res step ih =>
      intro ξ h0
      simpa using TLLC.Process.Step.res (ih (upRen_Chan_Chan ξ) rfl)
  | congr left step right ih =>
      intro ξ h0
      exact TLLC.Process.Step.congr (process_congr_crename left ξ) (ih ξ h0)
        (process_congr_crename right ξ)

lemma process_step_parallel_left {p q r : Proc}
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (.par p r) (.par q r) := by
  exact TLLC.Process.Step.congr
    (ARS.conv1 TLLC.Process.Congr.par_sym)
    (TLLC.Process.Step.par (o := r) step)
    (ARS.conv1 TLLC.Process.Congr.par_sym)

lemma process_step_parAll_accumulator {p q : Proc} (processes : List Proc)
    (step : TLLC.Process.Step p q) :
    TLLC.Process.Step (parAll p processes) (parAll q processes) := by
  induction processes generalizing p q with
  | nil =>
      simpa using step
  | cons process processes ih =>
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (process_step_parallel_left (r := process) step)

lemma process_congr_parAll_accumulator {p q : Proc} (processes : List Proc)
    (congr : TLLC.Process.Cong p q) :
    TLLC.Process.Cong (parAll p processes) (parAll q processes) := by
  induction processes generalizing p q with
  | nil =>
      simpa using congr
  | cons process processes ih =>
      simpa [parAll] using
        ih (p := .par p process) (q := .par q process)
          (process_congr_parallel_left (r := process) congr)

lemma process_step_parAll_list {body old new : Proc} (before after : List Proc)
    (step : TLLC.Process.Step old new) :
    TLLC.Process.Step
      (parAll body (before ++ old :: after))
      (parAll body (before ++ new :: after)) := by
  induction before generalizing body with
  | nil =>
      simpa [parAll] using
        process_step_parAll_accumulator after
          (TLLC.Process.Step.par (o := body) step)
  | cons process before ih =>
      simpa [parAll, List.cons_append] using
        ih (body := .par body process)

lemma process_step_comIm_edge_csubst {M N : EvalCtx} {payloadTerm : Term} {c d : Chan}
    (payload : implicitPayload c d payloadTerm) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        (.nu (.par
          (.tm (((M.eval (.app (.send (Term.chan c) .im) payloadTerm .im))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.recv (Term.chan d) .im))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))))
        (.nu (.par
          (.tm (((M.eval (.pure (Term.chan c)))[
            bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ; Term.var_Term]))
          (.tm (((N.eval (.pure (.pair payloadTerm (Term.chan d) .im .L)))[
            bindEndpointAt 0 d; Term.var_Term])[up_Chan_Chan σ; Term.var_Term])))) := by
  intro σ
  cases c with
  | var_Chan parentIndex =>
    cases d with
    | var_Chan childIndex =>
      have payloadEq :
          payloadTerm[(fun x => if x = parentIndex then Chan.var_Chan 0 else Chan.var_Chan (x + 1)) >>
              [Chan.var_Chan var_zero .: σ >> ⟨↑⟩]; Term.var_Term] =
            payloadTerm[(fun x => if x = childIndex then Chan.var_Chan 0 else Chan.var_Chan (x + 1)) >>
              [Chan.var_Chan var_zero .: σ >> ⟨↑⟩]; Term.var_Term] := by
        convert payload σ using 1 <;>
          (asimp; unfold bindEndpointAt chanIndex; simp)
      convert (TLLC.Process.Step.comIm
        (M := (M.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan parentIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (N := (N.cren (TLLC.Static.csubst_ren (bindEndpointAt 0 (Chan.var_Chan childIndex)))).cren
          (TLLC.Static.csubst_ren (up_Chan_Chan σ)))
        (m := payloadTerm[bindEndpointAt 0 (Chan.var_Chan parentIndex); Term.var_Term][up_Chan_Chan σ;
          Term.var_Term])) using 1
      all_goals
        repeat rw [evalctx_csubst]
        asimp
        unfold bindEndpointAt chanIndex
        simp
        try rw [← payloadEq]
        try constructor
        all_goals try trivial
        try asimp

lemma parAll_csubst (body : Proc) (processes : List Proc) :
    ∀ σ : Nat → Chan,
      (parAll body processes)[σ; Term.var_Term] =
        parAll (body[σ; Term.var_Term])
          (processes.map (fun process => process[σ; Term.var_Term])) := by
  induction processes generalizing body with
  | nil =>
    intro σ
    simp [parAll]
  | cons process processes ih =>
    intro σ
    simpa [parAll] using ih (.par body process) σ

lemma process_step_flattenSubtrees_list {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (step : TLLC.Process.Step subtree.flatten subtree'.flatten) :
    TLLC.Process.Step
      (parAll body (flattenSubtrees (before ++ subtree :: after)))
      (parAll body (flattenSubtrees (before ++ subtree' :: after))) := by
  simpa [flattenSubtrees_eq_map, List.map_append] using
    process_step_parAll_list (body := body)
      (before.map Tree.flatten) (after.map Tree.flatten) step

lemma process_step_flattenSubtrees_list_csubst {body : Proc} {subtree subtree' : Tree}
    (before after : List Tree)
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (subtree.flatten[σ; Term.var_Term])
        (subtree'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((parAll body (flattenSubtrees (before ++ subtree :: after)))[σ; Term.var_Term])
        ((parAll body (flattenSubtrees (before ++ subtree' :: after)))[σ; Term.var_Term]) := by
  intro σ
  rw [parAll_csubst]
  rw [parAll_csubst]
  simpa [flattenSubtrees_eq_map, List.map_append, List.map_map] using
    process_step_parAll_list (body := body[σ; Term.var_Term])
      ((before.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      ((after.map Tree.flatten).map (fun process => process[σ; Term.var_Term]))
      (step σ)

lemma process_step_flattenChildren_body_csubst {body body' : Proc}
    (children : List (Chan × Tree))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (body[σ; Term.var_Term]) (body'[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step ((flattenChildren body children)[σ; Term.var_Term])
        ((flattenChildren body' children)[σ; Term.var_Term]) := by
  induction children with
  | nil =>
      intro σ
      simpa [flattenChildren] using step σ
  | cons edge children ih =>
      intro σ
      rcases edge with ⟨c, child⟩
      rw [flattenChildren]
      rw [flattenChildren]
      cases h : child.flattenAt with
      | mk d childProcess =>
          have tailStep := ih (fun x => (bindEndpointAt 0 c x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := childProcess[bindEndpointAt 0 d; Term.var_Term][up_Chan_Chan σ;
                  Term.var_Term])
                tailStep)
            using 1
          · simp
            asimp
          · simp
            asimp

lemma process_step_flattenChildren_child_csubst {body : Proc} {c d : Chan}
    {child child' : Tree} (before after : List (Chan × Tree))
    (childAt : child.flattenAt = (d, child.flatten))
    (childAt' : child'.flattenAt = (d, child'.flatten))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (child.flatten[σ; Term.var_Term])
        (child'.flatten[σ; Term.var_Term])) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step
        ((flattenChildren body (before ++ (c, child) :: after))[σ; Term.var_Term])
        ((flattenChildren body (before ++ (c, child') :: after))[σ; Term.var_Term]) := by
  induction before generalizing body with
  | nil =>
      intro σ
      simp only [List.nil_append]
      have childStep := step (fun x => (bindEndpointAt 0 d x)[up_Chan_Chan σ])
      convert
        TLLC.Process.Step.res
          (TLLC.Process.Step.par
            (o := (((flattenChildren body after)[bindEndpointAt 0 c; Term.var_Term])[up_Chan_Chan σ;
              Term.var_Term]))
            childStep)
        using 1
      · simp [flattenChildren, childAt]
        asimp
      · simp [flattenChildren, childAt']
        asimp
  | cons edge before ih =>
      intro σ
      rcases edge with ⟨e, sibling⟩
      rw [List.cons_append]
      cases siblingAt : sibling.flattenAt with
      | mk f siblingProcess =>
          have tailStep := ih (body := body) (fun x => (bindEndpointAt 0 e x)[up_Chan_Chan σ])
          convert
            TLLC.Process.Step.res
              (process_step_parallel_left
                (r := siblingProcess[bindEndpointAt 0 f; Term.var_Term][up_Chan_Chan σ;
                  Term.var_Term])
                tailStep)
            using 1
          · simp [flattenChildren, siblingAt]
            asimp
          · simp [flattenChildren, siblingAt]
            asimp

lemma process_step_flattenChildren_body {body body' : Proc}
    (children : List (Chan × Tree))
    (step : ∀ σ : Nat → Chan,
      TLLC.Process.Step (body[σ; Term.var_Term]) (body'[σ; Term.var_Term])) :
    TLLC.Process.Step (flattenChildren body children) (flattenChildren body' children) := by
  convert process_step_flattenChildren_body_csubst children step Chan.var_Chan using 1 <;> asimp

/-- Lemma 5.86 for productive spawning-tree steps, strengthened under channel substitution. -/
theorem simulation_csubst {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (step : Step p q) :
    ∀ σ : Nat → Chan,
      TLLC.Process.Step (p.flatten[σ; Term.var_Term]) (q.flatten[σ; Term.var_Term]) := by
  induction step with
  | rootFork => sorry
  | nodeFork => sorry
  | rootWait => sorry
  | nodeWait => sorry
  | rootClose => sorry
  | nodeClose => sorry
  | rootSendEx => sorry
  | nodeSendEx => sorry
  | rootRecvEx => sorry
  | nodeRecvEx => sorry
  | rootSendIm implicitPayload => sorry
  | nodeSendIm implicitPayload => sorry
  | rootRecvIm implicitPayload => sorry
  | nodeRecvIm implicitPayload => sorry
  | nodeForward => sorry
  | rootChild stepChild ih =>
      rename_i m c child child' before after subtrees
      obtain ⟨rChild, AChild, typedChild⟩ := by
        cases typed with
        | inl typedRoot =>
            exact typedRoot.child_typedAt (c := c) (child := child) (by simp)
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩)
      cases typedChild with
      | node single has typedTerm typedChildren typedSubtrees =>
          rename_i Θ x mChild childrenChild subtreesChild
          intro σ
          have childAt :
              (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flattenAt =
                (.var_Chan x, (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flatten) := by
            simp
          have childAt' : child'.flattenAt = (.var_Chan x, child'.flatten) :=
            Step.node_flattenAt_eq stepChild
          have bodyStep :
              TLLC.Process.Step
                ((flattenChildren (.tm m)
                  (before ++ (c, Tree.node (.var_Chan x) mChild childrenChild subtreesChild) :: after))[σ;
                    Term.var_Term])
                ((flattenChildren (.tm m) (before ++ (c, child') :: after))[σ; Term.var_Term]) :=
            process_step_flattenChildren_child_csubst
              (body := .tm m) (c := c) (d := .var_Chan x)
              before after childAt childAt' childStep σ
          simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
            process_step_parAll_accumulator
              ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | nodeChild stepChild ih =>
      rename_i parent m c child child' before after subtrees
      obtain ⟨rChild, AChild, typedChild⟩ := by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact typedAtNode.child_typedAt (c := c) (child := child) (by simp)
      have childStep := ih (Or.inr ⟨rChild, AChild, typedChild⟩)
      cases typedChild with
      | node single has typedTerm typedChildren typedSubtrees =>
          rename_i Θ x mChild childrenChild subtreesChild
          intro σ
          have childAt :
              (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flattenAt =
                (.var_Chan x, (Tree.node (.var_Chan x) mChild childrenChild subtreesChild).flatten) := by
            simp
          have childAt' : child'.flattenAt = (.var_Chan x, child'.flatten) :=
            Step.node_flattenAt_eq stepChild
          have bodyStep :
              TLLC.Process.Step
                ((flattenChildren (.tm m)
                  (before ++ (c, Tree.node (.var_Chan x) mChild childrenChild subtreesChild) :: after))[σ;
                    Term.var_Term])
                ((flattenChildren (.tm m) (before ++ (c, child') :: after))[σ; Term.var_Term]) :=
            process_step_flattenChildren_child_csubst
              (body := .tm m) (c := c) (d := .var_Chan x)
              before after childAt childAt' childStep σ
          simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
            process_step_parAll_accumulator
              ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | rootSubtree stepSubtree ih =>
      rename_i m children subtree subtree' before after
      have subtreeStep := ih (by
        cases typed with
        | inl typedRoot =>
            exact Or.inl (typedRoot.subtree_typed (by simp))
        | inr typedAtRoot =>
            obtain ⟨r, A, typedAtRoot⟩ := typedAtRoot
            cases typedAtRoot)
      intro σ
      simpa [Tree.flatten_root, flattenBody] using
        process_step_flattenSubtrees_list_csubst (body := flattenChildren (.tm m) children)
          before after subtreeStep σ
  | nodeSubtree stepSubtree ih =>
      rename_i parent m children subtree subtree' before after
      have subtreeStep := ih (by
        cases typed with
        | inl typedNode =>
            cases typedNode
        | inr typedAtNode =>
            obtain ⟨r, A, typedAtNode⟩ := typedAtNode
            exact Or.inl (typedAtNode.subtree_typed (by simp)))
      intro σ
      simpa [Tree.flatten_node, flattenBody] using
        process_step_flattenSubtrees_list_csubst (body := flattenChildren (.tm m) children)
          before after subtreeStep σ
  | rootExpr termStep =>
      rename_i m m' children subtrees
      intro σ
      have bodyStep :
          TLLC.Process.Step ((flattenChildren (.tm m) children)[σ; Term.var_Term])
            ((flattenChildren (.tm m') children)[σ; Term.var_Term]) :=
        process_step_flattenChildren_body_csubst children (fun σ => by
          simpa using TLLC.Process.Step.exp (dynamic_step_csubst termStep σ)) σ
      simpa [Tree.flatten_root, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep
  | nodeExpr termStep =>
      rename_i parent m m' children subtrees
      intro σ
      have bodyStep :
          TLLC.Process.Step ((flattenChildren (.tm m) children)[σ; Term.var_Term])
            ((flattenChildren (.tm m') children)[σ; Term.var_Term]) :=
        process_step_flattenChildren_body_csubst children (fun σ => by
          simpa using TLLC.Process.Step.exp (dynamic_step_csubst termStep σ)) σ
      simpa [Tree.flatten_node, flattenBody, parAll_csubst] using
        process_step_parAll_accumulator
          ((flattenSubtrees subtrees).map (fun process => process[σ; Term.var_Term])) bodyStep

/-- Lemma 5.86 for productive spawning-tree steps. -/
theorem simulation {p q : Tree}
    (typed : Typed p ∨ ∃ r A, TypedAt r A p)
    (step : Step p q) :
    TLLC.Process.Step p.flatten q.flatten := by
  convert simulation_csubst typed step Chan.var_Chan using 1 <;> asimp

end TLLC.Spawning
