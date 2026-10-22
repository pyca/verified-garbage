module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Halving
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
public import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.HalvingPublic
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Halving
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Workspace
meta import VerifiedGarbage.Proof.Framework.X86.RelCT
meta import VerifiedGarbage.Proof.Dsa.X86.Generation.ArithmeticTimingState
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! Factor-of-two extraction scans a public bit capacity with secret masks. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86

def halvingTaint : VG.X86.Taint.T :=
  arithmeticTaint

private theorem init_certificate : ∃ hc,
    (VG.Taint.check taint halvingTaint
      (.block (Impl.Dsa.X86.Generation.halvingInit Impl.Dsa.X86.Generation.arithmeticLay)) hc).isSome = true :=
  ⟨_, by taint_decide⟩

private theorem step_certificate : ∃ hc,
    (VG.Taint.check taint halvingTaint
      (Impl.Dsa.X86.Generation.halvingStep Impl.Dsa.X86.Generation.arithmeticLay) hc).isSome = true :=
  ⟨_, by taint_decide⟩

theorem halving_init_ct : RelCT isa (VG.X86.Taint.Agree halvingTaint)
    (.block (Impl.Dsa.X86.Generation.halvingInit Impl.Dsa.X86.Generation.arithmeticLay)) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := init_certificate
  exact RelCT.taint (A := taint) halvingTaint (fun _ _ h => h) checked

theorem halving_step_ct : RelCT isa (VG.X86.Taint.Agree halvingTaint)
    (Impl.Dsa.X86.Generation.halvingStep Impl.Dsa.X86.Generation.arithmeticLay) (fun _ _ => True) := by
  obtain ⟨hc, checked⟩ := step_certificate
  exact RelCT.taint (A := taint) halvingTaint (fun _ _ h => h) checked

theorem halving_loop_ct {left right : State} {base : Addr} {bytes len count valueA valueB budget : Nat}
    {sp : BitVec 32} {args : Nat → Byte} (arrays : 2 ≤ count)
    (positive : 0 < budget) (bound : budget ≤ 16384) :
    RelCT isa (fun s t => TimedHalving base bytes len count valueA budget 0 sp args left s ∧
      TimedHalving base bytes len count valueB budget 0 sp args right t)
      (.loop (Impl.Dsa.X86.Generation.halvingStep Impl.Dsa.X86.Generation.arithmeticLay) .ne)
      (fun s t => TimedHalving base bytes len count valueA budget budget sp args left s ∧
        TimedHalving base bytes len count valueB budget budget sp args right t) :=
  VG.Proof.Dsa.X86.fixedLoop_relCT _ _ positive
    (fun _ _ => halving_step_ct.mono
      (fun _ _ h => h.1.arguments.agree h.2.arguments h.1.run.state.workspace h.2.run.state.workspace)
      (fun _ _ _ => trivial))
    (fun _ _ hk h => halving_step_public h arrays hk bound)
    (fun _ _ hk h => halving_step_public h arrays hk bound)

theorem halving_ct {base : Addr} {bytes len count : Nat} {sp : BitVec 32} {args : Nat → Byte}
    (arrays : 2 ≤ count) (bits : 32 * VG.Proof.Rsa.X86.KeyRt.kw len ≤ 16384) :
    RelCT isa (ArithmeticPair base bytes len count sp args)
      (Impl.Dsa.X86.Generation.halving Impl.Dsa.X86.Generation.arithmeticLay)
      (ArithmeticPair base bytes len count sp args) := by
  unfold Impl.Dsa.X86.Generation.halving
  intro a b tr ur af bf ⟨ws, wt, A, B⟩ E F
  have positive : 0 < 32 * VG.Proof.Rsa.X86.KeyRt.kw len := by have := ws.ws.wpos; omega
  cases E with
  | @seq _ _ _ u _ _ _ E₁ E₂ =>
    cases F with
    | @seq _ _ _ v _ _ _ F₁ F₂ =>
      have eq₁ := (halving_init_ct _ _ _ _ _ _ (A.agree B ws wt) E₁ F₁).1
      have left := VG.Proof.Dsa.X86.wp_result (halving_init_public ws arrays rfl A) E₁
      have right := VG.Proof.Dsa.X86.wp_result (halving_init_public wt arrays rfl B) F₁
      obtain ⟨eq₂, leftDone, rightDone⟩ := halving_loop_ct arrays positive bits _ _ _ _ _ _ ⟨left, right⟩ E₂ F₂
      exact ⟨by rw [eq₁, eq₂], leftDone.run.state.workspace, rightDone.run.state.workspace,
        leftDone.arguments, rightDone.arguments⟩

end VG.Proof.Dsa.X86.Generation
