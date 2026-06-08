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
  exact .exp emp.pctxSingle (.pure (.one emp .nil .nil))

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

/-- One-step structural congruence preserves typing in both directions (Coq `proc_congr0_type`). -/
lemma Typed.congr0 {p q} (cgr : Congr p q) : ∀ {Θ}, (Θ ⊩ p) ↔ (Θ ⊩ q) := by
  induction cgr with
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
        | exp rea tym =>
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
  | tail _ c ih => exact (Typed.congr0 c).mp (ih ty)
  | taili _ c ih => exact (Typed.congr0 c).mpr (ih ty)

/-! ## Subject reduction. -/

/-- Process reduction preserves typing (Coq `proc_sr`). -/
theorem Typed.sr {p q} (st : p ⇛ q) : ∀ {Θ}, Θ ⊩ p → Θ ⊩ q := by
  induction st with
  | exp dst =>
    intro Θ ty
    cases ty with | exp rea tym => exact .exp rea (tym.sr dst)
  | @fork A m m' N N' e1 e2 =>
    intro Θ ty
    subst e1; subst e2
    cases ty with
    | exp rea tyEval =>
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
        -- process-level split of the existing resources
        obtain ⟨real1, real2⟩ := rea.split mrgΘ'
        refine .res tyA' (.par (.split (r := false) mrgΘ'.sym) ?parent ?child)
        · -- parent: the continuation fed the returned channel
          refine .exp (.one real2) ?_
          refine tyCont (.one false (A⟨((· + 1) : Nat → Nat); (id : Nat → Nat)⟩) :: Θ2e) _
            (.pure (cvar 0)) (.oneR mrgE2) ?_
          exact Typed.conv (ARS.conv_sym eqA0) (.pure (chanAt0 emp2 tyA')) tyMA0
        · -- child: the fork body with its endpoint substituted in
          refine .exp (.one real1) ?_
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
          | exp reaR tyRDyn =>
            cases reaR with
            | none reaR' =>
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
          | exp reaS tySDyn =>
            cases reaS with
            | none reaS' =>
              obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyApp, _⟩ := evalCtx_inv tySDyn
              cases mrgS with
              | none mrgS' =>
                obtain ⟨_, _, _, tySend, _, _⟩ := appIm_inv tyApp
                obtain ⟨_, _, _, _, _, _, tyv⟩ := sendIm_inv tySend
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyv
                cases js
        | @split _ _ _ rS _ mrgΘ' =>
          cases tyS with
          | exp reaS tySDyn =>
            cases reaS with
            | one reaS' =>
              cases tyR with
              | exp reaR tyRDyn =>
                cases reaR with
                | one reaR' =>
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
                            refine .exp (.one reaS') ?_
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
                            refine .exp (.one reaR') ?_
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
          | exp reaR tyRDyn =>
            cases reaR with
            | none reaR' =>
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
          | exp reaS tySDyn =>
            cases reaS with
            | none reaS' =>
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
          | exp reaS tySDyn =>
            cases reaS with
            | one reaS' =>
              cases tyR with
              | exp reaR tyRDyn =>
                cases reaR with
                | one reaR' =>
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
                            sorry
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
          | exp reaR tyRDyn =>
            cases reaR with
            | none reaR' =>
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
          | exp reaS tySDyn =>
            cases reaS with
            | none reaS' =>
              obtain ⟨ΘS1, ΘS2, AS0, mrgS, tyCloseS, _⟩ := evalCtx_inv tySDyn
              cases mrgS with
              | none mrgS' =>
                obtain ⟨_, tyvS⟩ := close_inv tyCloseS
                obtain ⟨_, _, js, _, _⟩ := chan_inv tyvS
                cases js
        | @split _ _ _ rS _ mrgΘ' =>
          cases tyS with
          | exp reaS tySDyn =>
            cases reaS with
            | one reaS' =>
              cases tyR with
              | exp reaR tyRDyn =>
                cases reaR with
                | one reaR' =>
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
                            sorry
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
