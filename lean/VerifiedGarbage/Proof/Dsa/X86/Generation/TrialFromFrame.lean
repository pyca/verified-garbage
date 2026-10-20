module
public import Mathlib.Tactic.Set
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeInputArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialCheck
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialSpec
public import Aesop.BuiltinRules
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameInputs
public import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomContext
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeFrameKeep
import VerifiedGarbage.Proof.Dsa.X86.Generation.TrialInputsKeep

/-! # Trial division precedes candidate preparation and consumes no witnesses -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem trialFromFrame_ok {G : PrimeConfig} {frame stack : Addr} {words : Nat → BitVec 32} {used : Nat} {s : State}
    (R : PrimeFrameInputs G frame words used s)
    (T : TrialInputs (allocated 16 s) stack (words 22) (words 5) G.len (if G.len ≤ 128 then 512 else 1024))
    (sp : 16 ≤ (s.gpr .esp).toNat)
    (frameStack : Region.Disjoint ⟨frame, frameBytes⟩ ⟨stack, 16⟩)
    (large : 8161 < G.modulus) :
    WP isa (trialFromFrame G.len) s fun t => PrimeFrameInputs G frame words used t ∧
      t.gpr .eax = (if Spec.RsaKeyGen.obviouslyComposite (8 * G.len) G.modulus then 0 else 1) ∧
      Frame [⟨stack, 16⟩] s.mem t.mem ∧ Keeps trialRegs s t := by
  unfold trialFromFrame
  refine WP.seq (WP.mono (trialArgs_ok R.search R.slots) fun a ⟨si, di, mem, Ka⟩ => ?_)
  have Ta := T.keep (by exact mem) (keeps_allocated Ka (by decide) 16) (by decide)
  refine WP.mono (trialCheck_ok (by rw [Ka.1 _ (by decide)]; exact sp) Ta si di)
    fun t ⟨status, O, Kt⟩ => ?_
  rw [mem] at O
  have K : Keeps trialRegs s t := (Ka.mono (by decide)).trans Kt
  refine ⟨R.keep O K (by decide) (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact frameStack)
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact T.inputApart), ?_, O, K⟩
  have value : trialValue a (words 22) G.len = G.modulus := by
    unfold trialValue; rw [mem]; exact R.candidate
  rw [status, value]
  have entries : (if G.len ≤ 128 then 512 else 1024) = Spec.RsaKeyGen.trialPrimes (8 * G.len) := by
    unfold Spec.RsaKeyGen.trialPrimes
    by_cases small : G.len ≤ 128
    · rw [ite_eq_left small, ite_eq_right (by omega)]
    · rw [ite_eq_right small, ite_eq_left (by omega)]
  rw [entries, trialStatus_spec large]
end VG.Proof.Dsa.X86.Generation
