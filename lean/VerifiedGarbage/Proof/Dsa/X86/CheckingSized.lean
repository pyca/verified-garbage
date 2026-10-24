module

public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Proof.Dsa.X86.OutputFrame
public import VerifiedGarbage.Proof.Dsa.X86.ScheduleFrame
public import VerifiedGarbage.Proof.Dsa.X86.Checks
public import VerifiedGarbage.Proof.Framework.X86.Spill
import VerifiedGarbage.Proof.Dsa.X86.ShapeModuli
import VerifiedGarbage.Proof.Dsa.X86.ShapeSavedFrame
import VerifiedGarbage.Proof.Dsa.X86.Failure
import VerifiedGarbage.Proof.Dsa.X86.Result
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Proof.Dsa.X86.CallerBuffer
import VerifiedGarbage.Proof.Dsa.X86.GenerateParameters

/-! # The domain checker rejects bad shapes and returns the algebraic mask -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Mont.X86.Dynamic
open VG.Impl.Dsa.Layout VG.Impl.Dsa.X86 VG.Proof.Ecdsa.X86

theorem checkingSizedWith_spec {base : Addr} {size pLen qLen p q g : Nat}
    {s : State} {params : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (paramsLen : params.length = 2 * pLen + qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩)
    (compute : Nat → Nat → Prog isa) (I : Mem → Prop) (written : Nat) (hwritten : usedBytes≤written)
    (compute_ok : ∀ {t : State}, Moduli base size pLen qLen p q t →
      CallerBuffer t base size (.input .g) pLen → operandValue t base (.input .g) pLen=g →
      WP isa (compute pLen qLen) t fun u =>
        Moduli base size pLen qLen p q u ∧
        flagW base (Layout.field .mask) u=flagW base (Layout.field .mask) t &&&
          mask32 ((1<g ∧ g<p) ∧ (p-1)%q=0 ∧ g^q%p=1) ∧
        ScheduleFrame base written t u ∧ I u.mem) :
    WP isa (Generate.checkSizedWith compute pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes pLen qLen params then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base written s.mem sf.mem ∧
      (Spec.Dsa.checkParametersBytes pLen qLen params=true → I sf.mem) ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  have bound : 8248 ≤ size := by have H : 15712 ≤ size := extent; omega
  have value : Spec.Dsa.checkParametersBytes pLen qLen params =
      decide (Spec.Dsa.parametersValid ⟨p, q, g⟩) := by
    simp only [Spec.Dsa.checkParametersBytes, widths, paramsLen, paramsValue, decide_true,
      beq_self_eq_true, Bool.true_and]
  unfold Generate.checkSizedWith
  refine WP.seq (WP.mono (shapeModuli_ok scr extent widths P Q hp hq) fun t ⟨F, Z, M, K, O⟩ => ?_)
  by_cases valid : shapeValid p q
  · refine WP.ite false (by simp only [eval, Z, valid, decide_true, Bool.not_true])
      (fun h => Bool.noConfusion h) (fun _ => ?_)
    obtain ⟨Mt, _⟩ := M valid
    refine WP.seq (WP.mono (compute_ok Mt
      (G.keep_shape O K (by decide) (by decide))
      ((G.value_keep_shape O K (by decide) (by decide) bound).trans hg))
      fun u ⟨Mu, Fu, E, Invariant⟩ => ?_)
    have mask : flagW base (Layout.field .mask) u = mask32 (Spec.Dsa.parametersValid ⟨p, q, g⟩) := by
      rw [Fu, F]
      simp only [mask32, valid, ite_true, BitVec.allOnes_and, generationChecks_spec valid]
    refine WP.mono (result_ok Mu.scr Mu.saved (Spec.Dsa.parametersValid ⟨p, q, g⟩) mask)
      fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, ((K.mono (by decide)).trans E.keeps).trans (Kf.mono (by decide)), ?_, by rw [Of]; exact fun _ => Invariant, ?_⟩
    · rw [V, value]
      by_cases h : Spec.Dsa.parametersValid ⟨p, q, g⟩ <;> simp only [h, decide_true, decide_false, ite_true, ite_false] <;> rfl
    · rw [Of]
      intro a ha hstack
      exact (E.outside a ha (by rw [K.1 .esp (by decide)]; exact hstack)).trans
        ((shapeFrame_outside O) a (.inr (by have : 15712≤written := hwritten; omega)))
    · intro regs saved
      rw [Of]
      exact E.saved regs (shapeFrame_saved O saved)
  · refine WP.ite true (by simp only [eval, Z, valid, decide_false, Bool.not_false])
      (fun _ => ?_) (fun h => Bool.noConfusion h)
    have invalid : ¬ Spec.Dsa.parametersValid ⟨p, q, g⟩ :=
      fun h => valid (parametersValid_shape h)
    refine WP.mono (verifyFailure_ok t) fun sf ⟨V, Kf, Of⟩ => ?_
    refine ⟨?_, (K.mono (by decide)).trans (Kf.mono (by decide)), ?_, ?_, ?_⟩
    · rw [V, value]
      simp only [invalid, decide_false]
      rfl
    · rw [Of]
      intro a ha _
      exact (shapeFrame_outside O) a (.inr (by have : 15712≤written := hwritten; omega))
    · rw [value]
      simp only [invalid,decide_false,Bool.false_eq_true, false_implies]
    · intro regs saved
      rw [Of]
      exact shapeFrame_saved O saved

theorem checkingSized_spec {base : Addr} {size pLen qLen p q g : Nat}
    {s : State} {params : List Byte}
    (scr : Scr s base size) (extent : usedBytes ≤ size) (widths : Spec.Dsa.lengthsValid pLen qLen)
    (P : CallerBuffer s base size (.input .p) pLen)
    (Q : CallerBuffer s base size (.input .q) qLen)
    (G : CallerBuffer s base size (.input .g) pLen)
    (hp : operandValue s base (.input .p) pLen = p)
    (hq : operandValue s base (.input .q) qLen = q)
    (hg : operandValue s base (.input .g) pLen = g)
    (paramsLen : params.length = 2 * pLen + qLen)
    (paramsValue : Spec.Dsa.paramsBytes pLen qLen params = ⟨p, q, g⟩) :
    WP isa (Generate.checkSized pLen qLen) s fun sf =>
      (sf.gpr .eax).toNat = (if Spec.Dsa.checkParametersBytes pLen qLen params then 1 else 0) ∧
      Keeps powerClob s sf ∧ StackOutside (s.gpr .esp) base usedBytes s.mem sf.mem ∧
      ∀ regs, VG.X86.Spill.Saved s.mem (off base) regs Entry.savedRegisters →
        VG.X86.Spill.Saved sf.mem (off base) regs Entry.savedRegisters := by
  refine WP.mono (checkingSizedWith_spec scr extent widths P Q G hp hq hg paramsLen paramsValue
    Generate.parameters (fun _ => True) usedBytes (Nat.le_refl _) ?_) ?_
  · intro t M G hg
    exact WP.mono (generateParameters_ok M G hg) fun u ⟨M,F,E⟩ =>
      ⟨M,F,E.schedule (Nat.le_refl _),trivial⟩
  · intro t ⟨V,K,O,_,S⟩
    exact ⟨V,K,O,S⟩

end VG.Proof.Dsa.X86
