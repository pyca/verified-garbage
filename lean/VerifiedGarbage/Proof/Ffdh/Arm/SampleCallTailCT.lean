module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.SampleTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.SamplePowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.SampleCallTail
import VerifiedGarbage.Proof.Ffdh.Arm.ExchangeMain
import VerifiedGarbage.Proof.Bignum.Math
import VerifiedGarbage.Proof.Ffdh.Arm.RangeCT
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Bignum.Arm.WindowBlocksCT

public import VerifiedGarbage.Impl.Ffdh.Arm.KeyGenerate

/-! # Key-generation finish timing with shared exponentiation -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Spec.Rsa.Mont (numAt Operand)

theorem sampleCallPower_next {power : Prog isa} (law : SamplePowerLaw power) (s : State)
    {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true)
    (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (size : eb.length = l.width) (odd : p.P % 2 = 1)
    (h : SamplePowerInput p l slots eb s ∧ KeyCallMemory p s) :
    WP isa power s (KeyRangeInput p slots) := by
  refine WP.mono (law.correct s h.1.context h.2 stable h56 h32 h.1.ready h.1.modulus odd
    h.1.r2 h.1.exponent size) ?_
  rintro t ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.1.outputs.after rest, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  have large := h.1.ready.modulus
  rw [h.1.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem sampleCallTail_ct {power : Prog isa} (law : SamplePowerLaw power)
    {p : Inputs} {l : ScalarLayout p} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = l.width) (size2 : eb2.length = l.width)
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => (SamplePowerInput p l slots eb1 s ∧ KeyCallMemory p s) ∧
      (SamplePowerInput p l slots eb2 t ∧ KeyCallMemory p t) ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) (fun _ _ => True) := by
  have range := (inRange_ct (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.tail
  exact relCT_chain (law.ct stable h56 h32 size1 size2 odd)
    (sampleCallPower_next law · stable h32 h56 size1 odd)
    (sampleCallPower_next law · stable h32 h56 size2 odd)
    (relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY))

theorem sampleCallTail_law {power : Prog isa} (law : SamplePowerLaw power) :
    SampleTailLaw (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) where
  correct := sampleCallTail_ok law
  ct := sampleCallTail_ct law

end VG.Proof.Ffdh.Arm
