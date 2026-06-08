import TLLC.Process.CSubst
import TLLC.Process.Occurs

/-!
# Process subject reduction (self-dual single-channel encoding)

Port of `coq_session/proc_sr.v`: structural congruence preserves typing (`proc_congr0_type`,
`proc_congr_type`) and process reduction preserves typing (`proc_sr`). Adapted to the self-dual
single-channel encoding (see [[tllc-process-channel-encoding]]); the prerequisites
`Typed.exch`/`cweaken`/`cstrengthen`/`occursCount`/`procOccurs_cren` are the channel-machinery
lemmas of the Process layer.
-/

namespace TLLC.Process
open Autosubst Autosubst.Notation
open TLLC.Dynamic
open scoped TLLC.Static TLLC.Dynamic

/-- The empty process types the trivial returning thread `⟨return ()⟩`. -/
lemma PEmpty.return {Θ} (emp : PEmpty Θ) : Θ ⊩ Proc.tm (.pure .one) := by
  exact .exp (.pure (.one emp .nil .nil))

/-! ## Exchange involution and the `0`-channel non-occurrence. -/

/-- `exch_ren` is an involution. -/
lemma exch_ren_invol : funcomp exch_ren exch_ren = (id : Nat → Nat) := by
  funext x
  match x with
  | 0 => rfl
  | 1 => rfl
  | (_ + 2) => rfl

/-- `0` is out of range of the `+1` channel shift. -/
lemma iren0_succ : Iren 0 ((· + 1) : Nat → Nat) := fun x => Nat.succ_ne_zero x

/-! ## Structural congruence preserves typing. -/

lemma projMotive_wellSorted {Γ A B C i t s}
    (tyC : (Term.sig A B i t :: Γ) ⊢ C : .srt s)
    (wf : Static.Wf (Term.sig A B i t :: Γ)) :
    (B :: A :: Γ) ⊢
      C[Chan.var_Chan; Term.pair (.var_Term 1) (.var_Term 0) i t .:  (·+2) >> Term.var_Term]
      : .srt s := by
  cases wf with
  | @cons _ _ s0 wfΓ tyS =>
    obtain ⟨s1, r, ord1, ord2, tyA, tyB, _⟩ := Static.sig_inv tyS
    have wf2 : Static.Wf (B :: A :: Γ) := .cons (.cons wfΓ tyA) tyB
    have agr0 : (B :: A :: Γ) ⊢ funcomp Term.var_Term (· + 2) ⊣ Γ := by
      have h := ((Static.AgreeSubst.refl wfΓ).wk2 (s := s1) tyA).wk2 (s := r) tyB
      rwa [show (fun x => ((Term.var_Term x)⟨(id : Nat → Nat); ↑⟩)⟨(id : Nat → Nat); ↑⟩)
            = funcomp Term.var_Term (· + 2) from by funext x; asimp] at h
    have tyS' := (Static.Typed.sig ord1 ord2 tyA tyB).substitution agr0
    asimp at tyS'
    have tyv1 : (B :: A :: Γ) ⊢ Term.var_Term 1
        : A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] := by
      have h := Static.Typed.var wf2 (Static.Has.succ Static.Has.zero)
      rwa [show A⟨(id : Nat → Nat); ↑⟩⟨(id : Nat → Nat); ↑⟩
            = A[Chan.var_Chan; funcomp Term.var_Term (· + 2)] from by asimp; substify] at h
    have tyv0 : (B :: A :: Γ) ⊢ Term.var_Term 0
        : (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
            (Term.var_Term 1)..] := by
      have h := Static.Typed.var wf2 (Static.Has.zero (A := B))
      rwa [show B⟨(id : Nat → Nat); ↑⟩
            = (B[Chan.var_Chan; up_Term_Term (funcomp Term.var_Term (· + 2))])[Chan.var_Chan;
              (Term.var_Term 1)..] from by
              asimp; substify; congr 1; funext x; rcases x with _ | x <;> rfl] at h
    have agr : (B :: A :: Γ)
        ⊢ Term.pair (.var_Term 1) (.var_Term 0) i t .: funcomp Term.var_Term (· + 2)
        ⊣ (Term.sig A B i t :: Γ) :=
      agr0.wk1 (A := Term.sig A B i t) (Static.Typed.pair tyS' tyv1 tyv0)
    exact tyC.substitution agr

lemma CongrTerm.dyn {Θ Γ Δ m n A} (ty : Θ ⨾ Γ ⨾ Δ ⊢ m : A)
    (e : CongrTerm .ex m n) :
    Θ ⨾ Γ ⨾ Δ ⊢ n : A := by
  induction ty generalizing n with
  | @var Θ Γ Δ x s A emp wf hs hΔ =>
      cases e
      exact .var emp wf hs hΔ
  | @lamIm Θ Γ Δ A B m s k1 k2 tym ihm =>
      cases e with
      | lam eA em =>
          cases tym.wf with
          | @null _ _ _ sA _ tyA =>
              obtain ⟨t, tyB⟩ := tym.validity
              have tyA' := tyA.prd (ARS.star1 eA.pstep)
              have hm := Typed.ctx_conv0 (ARS.conv_sym eA.conv) tyA' (ihm em)
              exact .conv (Static.conv_pi (ARS.conv_sym eA.conv) .refl)
                (.lamIm k1 k2 hm) (.pi tyA tyB)
  | @lamEx Θ Γ Δ A B m s t k1 k2 tym ihm =>
      cases e with
      | lam eA em =>
          cases tym.wf with
          | @cons _ _ _ sA _ tyA =>
              obtain ⟨u, tyB⟩ := tym.validity
              have tyA' := tyA.prd (ARS.star1 eA.pstep)
              have hm := Typed.ctx_conv1 (ARS.conv_sym eA.conv) tyA' (ihm em)
              exact .conv (Static.conv_pi (ARS.conv_sym eA.conv) .refl)
                (.lamEx k1 k2 hm) (.pi tyA tyB)
  | @appIm Θ Γ Δ A B m n s tym tyn ihm =>
      cases e with
      | app em en =>
          obtain ⟨t, tyP⟩ := tym.validity
          obtain ⟨u, tyB, _⟩ := Static.pi_inv tyP
          have tyBn := tyB.subst tyn
          asimp at tyBn
          have tyn' := tyn.prd (ARS.star1 en.pstep)
          exact .conv (Static.conv_beta (ARS.conv_sym en.conv))
            (.appIm (ihm em) tyn') tyBn
  | @appEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n s mrgΘ mrgΔ tym tyn ihm ihn =>
      cases e with
      | app em en =>
          obtain ⟨t, tyP⟩ := tym.validity
          obtain ⟨u, tyB, _⟩ := Static.pi_inv tyP
          have tyBn := tyB.subst tyn.toStatic
          asimp at tyBn
          exact .conv (Static.conv_beta (ARS.conv_sym en.conv))
            (.appEx mrgΘ mrgΔ (ihm em) (ihn en)) tyBn
  | @pairIm Θ Γ Δ A B m n t tyS tym tyn ihn =>
      cases e with
      | pair em en =>
          obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
          have tym' := tym.prd (ARS.star1 em.pstep)
          have tyBm' := tyB.subst tym'
          asimp at tyBm'
          have hn : Θ ⨾ Γ ⨾ Δ ⊢ _ : B[Chan.var_Chan; _..] :=
            Typed.conv (Static.conv_beta em.conv) (ihn en) tyBm'
          exact .pairIm tyS tym' hn
  | @pairEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B m n t mrgΘ mrgΔ tyS tym tyn ihm ihn =>
      cases e with
      | pair em en =>
          obtain ⟨s, r, _, _, tyA, tyB, _⟩ := Static.sig_inv tyS
          have tym' := ihm em
          have tyBm' := tyB.subst tym'.toStatic
          asimp at tyBm'
          have hn : Θ2 ⨾ Γ ⨾ Δ2 ⊢ _ : B[Chan.var_Chan; _..] :=
            Typed.conv (Static.conv_beta em.conv) (ihn en) tyBm'
          exact .pairEx mrgΘ mrgΔ tyS tym' hn
  | @projIm Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
      cases e with
      | proj eC em en =>
          have tyC' := tyC.prd (ARS.star1 eC.pstep)
          have hwit := projMotive_wellSorted (i := .im) tyC' tyC.wf
          have hn := Typed.conv (Static.conv_subst _ eC.conv) (ihn en) hwit
          have eqC := ARS.conv_trans (Static.conv_subst _ (ARS.conv_sym eC.conv))
            (Static.conv_beta (ARS.conv_sym em.conv))
          exact .conv eqC (.projIm mrgΘ mrgΔ tyC' (ihm em) hn) (tyC.subst tym.toStatic)
  | @projEx Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrgΘ mrgΔ tyC tym tyn ihm ihn =>
      cases e with
      | proj eC em en =>
          have tyC' := tyC.prd (ARS.star1 eC.pstep)
          have hwit := projMotive_wellSorted (i := .ex) tyC' tyC.wf
          have hn := Typed.conv (Static.conv_subst _ eC.conv) (ihn en) hwit
          have eqC := ARS.conv_trans (Static.conv_subst _ (ARS.conv_sym eC.conv))
            (Static.conv_beta (ARS.conv_sym em.conv))
          exact .conv eqC (.projEx mrgΘ mrgΔ tyC' (ihm em) hn) (tyC.subst tym.toStatic)
  | @one Θ Γ Δ emp wf k =>
      cases e
      exact .one emp wf k
  | @tt Θ Γ Δ emp wf k =>
      cases e
      exact .tt emp wf k
  | @ff Θ Γ Δ emp wf k =>
      cases e
      exact .ff emp wf k
  | @ite Θ1 Θ2 Θ Γ Δ1 Δ2 Δ A m n1 n2 s mrgΘ mrgΔ tyA tym tyn1 tyn2 ihm ihn1 ihn2 =>
      cases e with
      | ite eA em en1 en2 =>
          have tyA' := tyA.prd (ARS.star1 eA.pstep)
          have h1 := tyA'.subst (Static.Typed.tt tym.wf.toStatic)
          have h2 := tyA'.subst (Static.Typed.ff tym.wf.toStatic)
          have hn1 := Typed.conv (Static.conv_subst _ eA.conv) (ihn1 en1) h1
          have hn2 := Typed.conv (Static.conv_subst _ eA.conv) (ihn2 en2) h2
          have eq := ARS.conv_trans (Static.conv_subst _ (ARS.conv_sym eA.conv))
            (Static.conv_beta (ARS.conv_sym em.conv))
          exact .conv eq (.ite mrgΘ mrgΔ tyA' (ihm em) hn1 hn2) (tyA.subst tym.toStatic)
  | @pure Θ Γ Δ m A tym ihm =>
      cases e with
      | pure em =>
          exact .pure (ihm em)
  | @mlet Θ1 Θ2 Θ Γ Δ1 Δ2 Δ m n A B s t mrgΘ mrgΔ tyB tym tyn ihm ihn =>
      cases e with
      | mlet em en =>
          exact .mlet mrgΘ mrgΔ tyB (ihm em) (ihn en)
  | @chan Θ Γ Δ r x A js wf k tyA =>
      cases e
      exact .chan js wf k tyA
  | @fork Θ Γ Δ A m tym ihm =>
      cases e with
      | fork eA em =>
          cases tym.wf with
          | @cons _ _ _ s _ tyCh =>
              obtain ⟨tyA, _⟩ := Static.ch_inv tyCh
              have tyA' := tyA.prd (ARS.star1 eA.pstep)
              have hm := Typed.ctx_conv1 (Static.conv_ch (ARS.conv_sym eA.conv))
                (Static.Typed.ch tyA') (ihm em)
              exact .conv (Static.conv_M (Static.conv_ch (ARS.conv_sym eA.conv)))
                (.fork hm) (Static.Typed.M (Static.Typed.ch tyA))
  | @recv Θ Γ Δ r1 r2 A B m i xor tym ihm =>
      cases e with
      | recv em =>
          exact .recv xor (ihm em)
  | @send Θ Γ Δ r1 r2 A B m i xor tym ihm =>
      cases e with
      | send em =>
          exact .send xor (ihm em)
  | @close Θ Γ Δ b m tym ihm =>
      cases e with
      | close em =>
          exact .close (ihm em)
  | @conv Θ Γ Δ A B m s eq tym tyB ihm =>
      exact .conv eq (ihm e) tyB

/-- One-step structural congruence preserves typing in both directions (Coq `proc_congr0_type`). -/
lemma Typed.congr_step {p q} (cgr : CongrProc p q) : ∀ {Θ}, (Θ ⊩ p) ↔ (Θ ⊩ q) := by
  induction cgr with
  | tm e =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | exp tym =>
          exact .exp (CongrTerm.dyn tym e)
    · intro ty
      cases ty with
      | exp tym =>
          exact .exp (CongrTerm.dyn tym e.sym)
  | @par_sym p q =>
    intro Θ
    constructor <;>
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg.sym t2 t1
  | @assoc o p q =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg1 ho tpq =>
        cases tpq with
        | par mrg2 tp tq =>
          obtain ⟨Θc, mc1, mc2⟩ := mrg1.sym.splitL mrg2
          exact .par mc2 (.par mc1.sym ho tp) tq
    · intro ty
      cases ty with
      | par mrg1 top tq =>
        cases top with
        | par mrg2 ho tp =>
          obtain ⟨Θc, mc1, mc2⟩ := mrg1.splitR mrg2
          exact .par mc2.sym ho (.par mc1 tp tq)
  | @scope p q =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg t1 t2 =>
        cases t1 with
        | res tyA tp => exact .res tyA (.par (.bothL mrg) tp t2.cweaken)
    · intro ty
      cases ty with
      | res tyA tpar =>
        cases tpar with
        | par mrg tp tq =>
          cases mrg with
          | bothL mrg' => exact .par mrg' (.res tyA tp) tq.cstrengthen
          | bothR mrg' =>
            have h1 := tq.occursCount 0
            rw [procOccurs_cren iren0_succ q] at h1
            exact absurd h1 (by simp [pcount])
          | split mrg' =>
            have h1 := tq.occursCount 0
            rw [procOccurs_cren iren0_succ q] at h1
            exact absurd h1 (by simp [pcount])
  | @exch p =>
    intro Θ
    constructor
    · intro ty
      rw [csubst_exch]
      exact ty.exch
    · intro ty
      have h := ty.exch
      rw [show (p[Process.exch; Term.var_Term])⟨exch_ren; (id : Nat → Nat)⟩ = p from by
            rw [csubst_exch]; asimp; rw [exch_ren_invol]; asimp] at h
      exact h
  | @par p p' q q' _ _ ihp ihq =>
    intro Θ
    constructor
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg (ihp.mp t1) (ihq.mp t2)
    · intro ty; cases ty with | par mrg t1 t2 => exact .par mrg (ihp.mpr t1) (ihq.mpr t2)
  | @res p p' _ ih =>
    intro Θ
    constructor
    · intro ty; cases ty with | res tyA tp => exact .res tyA (ih.mp tp)
    · intro ty; cases ty with | res tyA tp => exact .res tyA (ih.mpr tp)
  | @«end» p =>
    intro Θ
    constructor
    · intro ty
      cases ty with
      | par mrg t1 t2 =>
        cases t2 with
        | exp tym =>
          obtain ⟨B, ty1, _⟩ := pure_invX tym
          have emp := one_inv ty1
          have e := mrg.emptyR emp
          rw [e] at t1; exact t1
    · intro ty
      obtain ⟨Θe, emp, mrg⟩ := PMerge.refl_emptyR Θ
      exact .par mrg ty (PEmpty.return emp)

/-- Structural congruence preserves typing (Coq `proc_congr_type`). -/
lemma Typed.congr {Θ p q} (ty : Θ ⊩ p) (e : p ≡ₚ q) : Θ ⊩ q := by
  induction e generalizing Θ with
  | refl => exact ty
  | tail _ c ih => exact (Typed.congr_step c).mp (ih ty)
  | taili _ c ih => exact (Typed.congr_step c).mpr (ih ty)

/-! ## Subject reduction. -/

/-- Process reduction preserves typing (Coq `proc_sr`). -/
theorem Typed.sr {p q} (st : p ⇛ q) : ∀ {Θ}, Θ ⊩ p → Θ ⊩ q := by
  induction st with
  | exp dst =>
    intro Θ ty
    cases ty with | exp tym => exact .exp (tym.sr dst)
  | @fork A m m' N N' e1 e2 =>
    intro Θ ty
    subst e1; subst e2
    cases ty with
    | exp tyEval =>
      -- shift the whole thread under the fresh ν, then split off the redex
      have tyW := tyEval.cweaken
      rw [evalctx_cren] at tyW
      rw [show (Term.fork A m)⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩
            = Term.fork (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩)
                (m⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) from by asimp] at tyW
      obtain ⟨Θ1, Θ2, A0, mrgΘ, tyFork, tyCont⟩ := evalCtx_inv tyW
      cases mrgΘ with
      | none mrgΘ' =>
        obtain ⟨tyBody, eqA0⟩ := fork_inv tyFork
        -- `A' = A⟨↑⟩` is the (closed) protocol of the fresh channel
        obtain ⟨sM, tyMA0⟩ := tyFork.validity
        have tyA' : [] ⊢ A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩ : .proto := by
          cases tyBody.wf with
          | cons _ tyChA' => exact (Static.ch_inv tyChA').1
        -- well-formedness → empty right-identities for the two threads
        have wfd := tyEval.procWf
        obtain ⟨wf1, wf2⟩ := ProcWf.merge_inv mrgΘ' wfd
        obtain ⟨Θ1e, emp1, mrgE1⟩ := procWf_emptyR wf1
        obtain ⟨Θ2e, emp2, mrgE2⟩ := procWf_emptyR wf2
        refine .res tyA' (.par (.split (r := false) mrgΘ'.sym) ?parent ?child)
        · -- parent: the continuation fed the returned channel
          refine .exp ?_
          refine tyCont (.one false (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) :: Θ2e) _
            (.pure (cvar 0)) (.oneR mrgE2) ?_
          exact Typed.conv (ARS.conv_sym eqA0) (.pure (chanAt0 emp2 tyA')) tyMA0
        · -- child: the fork body with its endpoint substituted in
          refine .exp ?_
          exact Typed.esubst1 rfl (by asimp) PKey.impure (.oneR mrgE1)
            Key.nil Merge.nil tyBody (chanAt0 emp1 tyA')
  | @comIm M N m =>
    intro Θ ty
    cases ty with
    | res tyA tyPar =>
      cases tyPar with
      | par mrgPar tyS tyR =>
        cases mrgPar with
        | bothL mrgΘ' =>
            -- receiver references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyR with
            | exp tyRDyn =>
              obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyRecv, _⟩ := evalCtx_inv tyRDyn
              cases mrgR with
              | none mrgR' =>
                obtain ⟨_, _, _, _, _, _, tyv⟩ := recvIm_inv tyRecv
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyv
                cases js
        | bothR mrgΘ' =>
            -- sender references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyS with
            | exp tySDyn =>
              obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyApp, _⟩ := evalCtx_inv tySDyn
              cases mrgS with
              | none mrgS' =>
                obtain ⟨_, _, _, tySend, _, _⟩ := appIm_inv tyApp
                obtain ⟨_, _, _, _, _, _, tyv⟩ := sendIm_inv tySend
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyv
                cases js
          | @split _ _ _ rS _ mrgΘ' =>
            cases tyS with
            | exp tySDyn =>
              cases tyR with
              | exp tyRDyn =>
                obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyApp, tyContS⟩ := evalCtx_inv tySDyn
                obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyRecv, tyContR⟩ := evalCtx_inv tyRDyn
                obtain ⟨AS, BS, sS, tySend, tyMsg, eqApp⟩ := appIm_inv tyApp
                obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendIm_inv tySend
                obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvIm_inv tyRecv
                -- pin each endpoint onto the single channel slot
                cases mrgS with
                | oneR _ => obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS; cases js
                | @oneL ΘSa ΘSb _ _ _ mrgS' =>
                  cases mrgR with
                  | oneR _ => obtain ⟨_, _, js, _, _⟩ := chan_inv tyvR; cases js
                  | @oneL ΘRa ΘRb _ _ _ mrgR' =>
                    obtain ⟨rJS, AJS, jsS, _, eqChS⟩ := chan_inv tyvS
                    obtain ⟨rJR, AJR, jsR, _, eqChR⟩ := chan_inv tyvR
                    cases jsS with
                    | zero empS =>
                      cases jsR with
                      | zero empR =>
                        -- protocol facts: `A ≃ act …`, message type, continuation `BBs[m..]`
                        obtain ⟨ers1, eactS⟩ := Static.ch_inj eqChS
                        obtain ⟨err1, eactR⟩ := Static.ch_inj eqChR
                        subst ers1; subst err1
                        obtain ⟨eAAsr, eBBsr, _, _⟩ :=
                          Static.act_inj (ARS.conv_trans eactS (ARS.conv_sym eactR))
                        obtain ⟨_, tyChS⟩ := tyvS.validity
                        obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
                        have tyBBs := Static.act_inv tyActS
                        obtain ⟨_, tyAAs⟩ : ∃ s, [] ⊢ AAs : Term.srt s := by
                          cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
                        obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
                        have tyMsgA : [] ⊢ m : AAs := Static.Typed.conv eAS tyMsg tyAAs
                        have tyP : [] ⊢ BBs[Chan.var_Chan; m..] : .proto := by
                          have h := tyBBs.subst tyMsgA; asimp at h; exact h
                        obtain ⟨_, tyMAS0⟩ := tyApp.validity
                        -- empty right-identities for the post-redex resources
                        have eS := mrgS'.emptyL empS; subst eS
                        have wfS' : ProcWf ΘSb := by cases tySDyn.procWf with | one w _ => exact w
                        obtain ⟨ΘSe, empSe, mrgSe⟩ := procWf_emptyR wfS'
                        refine .res tyP (.par (.split (r := rs1) mrgΘ') ?sender ?recv)
                        · -- sender: returns the (advanced) channel
                          refine .exp ?_
                          refine tyContS (.one rs1 (BBs[Chan.var_Chan; m..]) :: ΘSe) _
                            (.pure (cvar 0)) (.oneR mrgSe) ?_
                          refine Typed.conv ?_ (.pure (chanAt0 empSe tyP)) tyMAS0
                          refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
                          exact Static.conv_subst (m..) eBS
                        · -- receiver: returns the message paired with the (advanced) channel
                          obtain ⟨_, tyChR⟩ := tyvR.validity
                          obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
                          have tyBBr := Static.act_inv tyActR
                          obtain ⟨_, tyAAr⟩ : ∃ s, [] ⊢ AAr : Term.srt s := by
                            cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
                          have tyMsgR : [] ⊢ m : AAr := Static.Typed.conv (ARS.conv_trans eAS eAAsr) tyMsg tyAAr
                          have eR := mrgR'.emptyL empR; subst eR
                          have wfR' : ProcWf ΘRb := by cases tyRDyn.procWf with | one w _ => exact w
                          obtain ⟨ΘRe, empRe, mrgRe⟩ := procWf_emptyR wfR'
                          obtain ⟨_, tyMAR0⟩ := tyRecv.validity
                          refine .exp ?_
                          refine tyContR (.one (!rs1) (BBs[Chan.var_Chan; m..]) :: ΘRe) _
                            (.pure (.pair m (cvar 0) .im .L)) (.oneR mrgRe) ?_
                          refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
                          refine Typed.pairIm
                            (Static.Typed.sig (by nofun) Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
                            tyMsgR ?_
                          refine Typed.conv (s := .L) (Static.conv_ch (Static.conv_subst (m..) eBBsr))
                            (chanAt0 empRe tyP) ?_
                          have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR)
                          asimp at h ⊢; exact h
  | @comEx M N v vv =>
    intro Θ ty
    cases ty with
    | res tyA tyPar =>
      cases tyPar with
      | par mrgPar tyS tyR =>
        cases mrgPar with
        | bothL mrgΘ' =>
            -- receiver references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyR with
            | exp tyRDyn =>
              obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyRecv, _⟩ := evalCtx_inv tyRDyn
              cases mrgR with
              | none mrgR' =>
                obtain ⟨_, _, _, _, _, _, tyv⟩ := recvEx_inv tyRecv
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyv
                cases js
        | bothR mrgΘ' =>
            -- sender references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyS with
            | exp tySDyn =>
              obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyApp, _⟩ := evalCtx_inv tySDyn
              cases mrgS with
              | none mrgS' =>
                obtain ⟨AS, BS, sS, ΘF, ΘV, ΔF, ΔV, mrgAppΘ, mrgAppΔ, tySend, _, _⟩ :=
                  appEx_inv tyApp
                cases mrgAppΔ
                cases mrgAppΘ with
                | none mrgAppΘ' =>
                  obtain ⟨_, _, _, _, _, _, tyv⟩ := sendEx_inv tySend
                  obtain ⟨_, _, js, _, _⟩ := chan_inv tyv
                  cases js
          | @split _ _ _ rS _ mrgΘ' =>
            cases tyS with
            | exp tySDyn =>
              cases tyR with
              | exp tyRDyn =>
                obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyApp, tyContS⟩ := evalCtx_inv tySDyn
                obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyRecv, tyContR⟩ := evalCtx_inv tyRDyn
                obtain ⟨AS, BS, sS, ΘSF, ΘSV, ΔSF, ΔSV, mrgAppΘ, mrgAppΔ, tySend, tyMsg, eqApp⟩ :=
                  appEx_inv tyApp
                cases mrgAppΔ
                obtain ⟨rs1, rs2, AAs, BBs, xorS, eqPiS, tyvS⟩ := sendEx_inv tySend
                obtain ⟨rr1, rr2, AAr, BBr, xorR, eqMR, tyvR⟩ := recvEx_inv tyRecv
                -- pin each endpoint onto the single channel slot, then move the explicit
                -- message resources from the sender side to the receiver side.
                cases mrgS with
                | oneR _ =>
                  cases mrgAppΘ with
                  | none mrgAppΘ' =>
                    obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS
                    cases js
                | @oneL ΘSa ΘSb _ _ _ mrgS' =>
                  cases mrgAppΘ with
                  | oneR _ =>
                    obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS
                    cases js
                  | @oneL ΘSFa ΘSVa _ _ _ mrgAppΘ' =>
                    cases mrgR with
                    | oneR _ => obtain ⟨_, _, js, _, _⟩ := chan_inv tyvR; cases js
                    | @oneL ΘRa ΘRb _ _ _ mrgR' =>
                      obtain ⟨rJS, AJS, jsS, _, eqChS⟩ := chan_inv tyvS
                      obtain ⟨rJR, AJR, jsR, _, eqChR⟩ := chan_inv tyvR
                      cases jsS with
                      | zero empS =>
                        cases jsR with
                        | zero empR =>
                          -- protocol facts: `A ≃ act …`, message type, continuation `BBs[v..]`
                          have eApp := mrgAppΘ'.emptyL empS; subst eApp
                          obtain ⟨ers1, eactS⟩ := Static.ch_inj eqChS
                          obtain ⟨err1, eactR⟩ := Static.ch_inj eqChR
                          subst ers1; subst err1
                          obtain ⟨eAAsr, eBBsr, _, _⟩ :=
                            Static.act_inj (ARS.conv_trans eactS (ARS.conv_sym eactR))
                          obtain ⟨_, tyChS⟩ := tyvS.validity
                          obtain ⟨tyActS, _⟩ := Static.ch_inv tyChS
                          have tyBBs := Static.act_inv tyActS
                          obtain ⟨_, tyAAs⟩ : ∃ s, [] ⊢ AAs : Term.srt s := by
                            cases tyBBs.wf with | cons _ h => exact ⟨_, h⟩
                          obtain ⟨eAS, eBS, _, _⟩ := Static.pi_inj eqPiS
                          have tyMsgA : (Slot.none :: ΘSVa) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAs :=
                            Typed.conv eAS tyMsg tyAAs
                          have tyP : [] ⊢ BBs[Chan.var_Chan; v..] : .proto := by
                            have h := tyBBs.subst tyMsgA.toStatic; asimp at h; exact h
                          obtain ⟨_, tyMAS0⟩ := tyApp.validity
                          have eR := mrgR'.emptyL empR; subst eR
                          obtain ⟨wfMsg, wfCont⟩ :=
                            ProcWf.merge_inv mrgS' (by cases tySDyn.procWf with | one w _ => exact w)
                          obtain ⟨ΘSe, empSe, mrgSe⟩ := procWf_emptyR wfCont
                          obtain ⟨ΘVe, empVe, mrgVe⟩ := procWf_emptyR wfMsg
                          obtain ⟨ΘRecvP, mrgMsgRecv, mrgRecvContRev⟩ := mrgΘ'.splitL mrgS'
                          have mrgContRecv : PMerge ΘSb ΘRecvP Θ := mrgRecvContRev.sym
                          have tySender :
                              (Slot.one rs1 (BBs[Chan.var_Chan; v..]) :: ΘSb) ⊩
                                Proc.tm (M.eval (.pure (cvar 0))) := by
                            refine .exp ?_
                            refine tyContS (.one rs1 (BBs[Chan.var_Chan; v..]) :: ΘSe) _
                              (.pure (cvar 0)) (.oneR mrgSe) ?_
                            refine Typed.conv ?_ (.pure (chanAt0 empSe tyP)) tyMAS0
                            refine ARS.conv_sym (ARS.conv_trans eqApp ?_)
                            exact Static.conv_subst (v..) eBS
                          have tyReceiver :
                              (Slot.one (!rs1) (BBs[Chan.var_Chan; v..]) :: ΘRecvP) ⊩
                                Proc.tm (N.eval (.pure (.pair v (cvar 0) .ex .L))) := by
                            obtain ⟨_, tyChR⟩ := tyvR.validity
                            obtain ⟨tyActR, _⟩ := Static.ch_inv tyChR
                            have tyBBr := Static.act_inv tyActR
                            obtain ⟨_, tyAAr⟩ : ∃ s, [] ⊢ AAr : Term.srt s := by
                              cases tyBBr.wf with | cons _ h => exact ⟨_, h⟩
                            have tyMsgR :
                                (Slot.none :: ΘSVa) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢ v : AAr :=
                              Typed.conv eAAsr tyMsgA tyAAr
                            obtain ⟨_, tyMAR0⟩ := tyRecv.validity
                            have tyPayload :
                                (Slot.one (!rs1) (BBs[Chan.var_Chan; v..]) :: ΘSVa) ⨾
                                    ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                                  .pure (.pair v (cvar 0) .ex .L) : AR0.M := by
                              refine Typed.conv (ARS.conv_sym eqMR) (.pure ?_) tyMAR0
                              refine Typed.pairEx (.oneR mrgVe) .nil
                                (Static.Typed.sig (fun _ => Static.sort_leq_Lgt)
                                  Static.sort_leq_Lgt tyAAr (Static.Typed.ch tyBBr))
                                tyMsgR ?_
                              refine Typed.conv (s := .L)
                                (Static.conv_ch (Static.conv_subst (v..) eBBsr))
                                (chanAt0 empVe tyP) ?_
                              have h := Static.Typed.ch (b := !rs1) (tyBBr.subst tyMsgR.toStatic)
                              asimp at h ⊢; exact h
                            refine .exp ?_
                            exact tyContR (.one (!rs1) (BBs[Chan.var_Chan; v..]) :: ΘSVa) _
                              (.pure (.pair v (cvar 0) .ex .L)) (.oneR mrgMsgRecv.sym) tyPayload
                          exact .res tyP (.par (.split (r := rs1) mrgContRecv) tySender tyReceiver)
  | @«end» M N M' N' e1 e2 =>
    intro Θ ty
    subst e1; subst e2
    cases ty with
    | res tyA tyPar =>
      cases tyPar with
      | par mrgPar tyS tyR =>
        cases mrgPar with
        | bothL mrgΘ' =>
            -- receiver references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyR with
            | exp tyRDyn =>
              obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyCloseR, _⟩ := evalCtx_inv tyRDyn
              cases mrgR with
              | none mrgR' =>
                obtain ⟨_, tyvR⟩ := wait_inv tyCloseR
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyvR
                cases js
        | bothR mrgΘ' =>
            -- sender references `cvar 0` on an absent slot — impossible
            exfalso
            cases tyS with
            | exp tySDyn =>
              obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyCloseS, _⟩ := evalCtx_inv tySDyn
              cases mrgS with
              | none mrgS' =>
                obtain ⟨_, tyvS⟩ := close_inv tyCloseS
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS
                cases js
          | @split _ _ _ rS _ mrgΘ' =>
            cases tyS with
            | exp tySDyn =>
              cases tyR with
              | exp tyRDyn =>
                obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyCloseS, tyContS⟩ := evalCtx_inv tySDyn
                obtain ⟨ΘR1, ΘR2, AR0, mrgR, tyCloseR, tyContR⟩ := evalCtx_inv tyRDyn
                obtain ⟨eqCloseS, tyvS⟩ := close_inv tyCloseS
                obtain ⟨eqCloseR, tyvR⟩ := wait_inv tyCloseR
                cases mrgS with
                | oneR _ => obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS; cases js
                | @oneL ΘSa ΘSb _ _ _ mrgS' =>
                  cases mrgR with
                  | oneR _ => obtain ⟨_, _, js, _, _⟩ := chan_inv tyvR; cases js
                  | @oneL ΘRa ΘRb _ _ _ mrgR' =>
                    obtain ⟨rJS, AJS, jsS, _, eqChS⟩ := chan_inv tyvS
                    obtain ⟨rJR, AJR, jsR, _, eqChR⟩ := chan_inv tyvR
                    cases jsS with
                    | zero empS =>
                      cases jsR with
                      | zero empR =>
                        have eS := mrgS'.emptyL empS; subst eS
                        have eR := mrgR'.emptyL empR; subst eR
                        have wfS' : ProcWf ΘSb := by
                          cases tySDyn.procWf with | one w _ => exact w
                        have wfR' : ProcWf ΘRb := by
                          cases tyRDyn.procWf with | one w _ => exact w
                        obtain ⟨ΘSe, empSe, mrgSe⟩ := procWf_emptyR wfS'
                        obtain ⟨ΘRe, empRe, mrgRe⟩ := procWf_emptyR wfR'
                        refine .par mrgΘ' ?senderEnd ?recvEnd
                        · refine .exp ?_
                          have tyUnitS :
                              (Slot.none :: ΘSe) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                                .pure .one : AS0.M := by
                            obtain ⟨_, tyMAS0⟩ := tyCloseS.validity
                            refine Typed.conv (ARS.conv_sym eqCloseS)
                              (.pure (.one (.none empSe) .nil .nil)) tyMAS0
                          have h := tyContS (Slot.none :: ΘSe) (Slot.none :: ΘSb)
                            (.pure .one) (.none mrgSe) tyUnitS
                          have h' := h.crename (Θ' := ΘSb)
                            (ξ := funcomp (id : Nat → Nat) (· - 1)) (.minus .O)
                          rw [evalctx_cren] at h'
                          asimp at h'
                          exact h'
                        · refine .exp ?_
                          have tyUnitR :
                              (Slot.none :: ΘRe) ⨾ ([] : Static.Ctx) ⨾ ([] : Ctx) ⊢
                                .pure .one : AR0.M := by
                            obtain ⟨_, tyMAR0⟩ := tyCloseR.validity
                            refine Typed.conv (ARS.conv_sym eqCloseR)
                              (.pure (.one (.none empRe) .nil .nil)) tyMAR0
                          have h := tyContR (Slot.none :: ΘRe) (Slot.none :: ΘRb)
                            (.pure .one) (.none mrgRe) tyUnitR
                          have h' := h.crename (Θ' := ΘRb)
                            (ξ := funcomp (id : Nat → Nat) (· - 1)) (.minus .O)
                          rw [evalctx_cren] at h'
                          asimp at h'
                          exact h'
  | par _ ih =>
    intro Θ ty
    cases ty with | par mrg ho tp => exact .par mrg ho (ih tp)
  | res _ ih =>
    intro Θ ty
    cases ty with | res tyA tp => exact .res tyA (ih tp)
  | congr cpp _ cqq ih =>
    intro Θ ty
    exact (ih (ty.congr cpp)).congr cqq

end TLLC.Process
