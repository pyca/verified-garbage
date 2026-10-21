module

import VerifiedGarbage.Proof.Bignum.Arm.StackCT

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentTailLaw
public import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentPowerLaw
import VerifiedGarbage.Proof.Ffdh.Arm.EnvironmentCallTail
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

theorem environmentCallPower_next {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power) (s : State)
    {p : Inputs} {slots : List Nat} {eb : List Byte}
    (stable : stableSlots slots = true)
    (h52 : 52 ∈ slots) (h32 : 32 ∈ slots) (h56 : 56 ∈ slots) (size : eb.length = (layout p).width) (exponentFits : Spec.Rsa.os2ip eb < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (odd : p.P % 2 = 1)
    (h : (SamplePowerInput p (layout p) slots eb s ∧ KeyCallMemory p s) ∧ env.holds p s) :
    WP isa power s (KeyRangeInput p slots) := by
  refine WP.mono (law.correct s h.1.1.context h.2 h.1.2 stable h52 h56 h32 h.1.1.ready h.1.1.modulus odd
    h.1.1.r2 h.1.1.exponent size exponentFits) ?_
  rintro t ⟨context, ready, value, modulus, _, _, _, rest⟩
  refine ⟨⟨context, ready, h.1.1.outputs.after rest, ?_⟩, modulus⟩
  rw [value, VG.Proof.Bignum.powMod_eq]
  have large := h.1.1.ready.modulus
  rw [h.1.1.modulus] at large
  exact Nat.lt_trans (Nat.mod_lt _ (by omega)) p.modulusBound

theorem environmentCallTail_ct {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power)
    {p : Inputs} {slots : List Nat} {eb1 eb2 : List Byte}
    (stable : stableSlots slots = true) (h52 : 52 ∈ slots) (h4 : 4 ∈ slots) (h32 : 32 ∈ slots)
    (h36 : 36 ∈ slots) (h40 : 40 ∈ slots) (h56 : 56 ∈ slots)
    (saved : ∀ d ∈ slots, d + 4 ≤ 64 ∨ 68 ≤ d)
    (size1 : eb1.length = (layout p).width) (size2 : eb2.length = (layout p).width)
    (fit1 : Spec.Rsa.os2ip eb1 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (fit2 : Spec.Rsa.os2ip eb2 < 2 ^ Spec.Ffdh.generationScalarBits (Spec.Ffdh.domainOf p.k p.dom))
    (odd : p.P % 2 = 1) (outputY : p.output = p.publicValue) :
    RelCT isa (fun s t => ((SamplePowerInput p (layout p) slots eb1 s ∧ KeyCallMemory p s) ∧ env.holds p s) ∧
      ((SamplePowerInput p (layout p) slots eb2 t ∧ KeyCallMemory p t) ∧ env.holds p t) ∧ env.publicRel s t ∧ s.sp = t.sp)
      (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) (fun _ _ => True) := by
  have range := (inRange_ct (by simp [Operand, Spec.Rsa.Mont.aAcc, Spec.Rsa.Mont.aTmp] : Operand 6) (by decide)).mono
    (P' := fun (s t : State) => KeyRangeInput p slots s ∧ KeyRangeInput p slots t ∧ s.sp = t.sp)
    (fun _ _ h => ⟨h.1.ready, h.2.1.ready, h.2.2⟩) (fun _ _ h => h)
  unfold VG.Impl.Ffdh.Arm.KeyGenerate.tail
  exact ((relCT_keep_sp (law.ct stable h52 h56 h32 size1 size2 fit1 fit2 odd)
      (fun _ _ h => h.2.2.2)).wp (fun s t h =>
        ⟨environmentCallPower_next law s stable h52 h32 h56 size1 fit1 odd h.1,
         environmentCallPower_next law t stable h52 h32 h56 size2 fit2 odd h.2.1⟩)).seq
    ((relCT_chain range (keyRange_next · stable odd) (keyRange_next · stable odd)
      (keyExportFinish_ct stable h4 h32 h36 h40 saved outputY)).mono
        (fun _ _ h => ⟨h.2.1, h.2.2, h.1⟩) (fun _ _ h => h))

theorem environmentCallTail_law {env : SampleEnvironment} {layout : (p : Inputs) → ScalarLayout p}
    {power : Prog isa} (law : EnvironmentPowerLaw env layout power) :
    EnvironmentTailLaw env layout (VG.Impl.Ffdh.Arm.KeyGenerate.tail power) where
  correct := environmentCallTail_ok law
  ct := environmentCallTail_ct law

end VG.Proof.Ffdh.Arm
