module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInit
import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import Init.Data.BitVec.BasicAux
public import VerifiedGarbage.Spec.Ffdh.Generation

/-! Relate the ARMv7 guard to the shared initialization specification. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG

theorem generatorNat (g : BitVec 32) (n : Nat) (hn : n < 2 ^ 32) :
    g.toNat = n ↔ g = BitVec.ofNat 32 n := by
  constructor
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn, h]
  · intro h
    rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem parameterInit_spec (bits gen : BitVec 32) :
    Spec.Ffdh.parameterInit bits.toNat gen.toNat =
      if 512 ≤ bits.toNat ∧ bits.toNat ≤ 8192 ∧ (gen = 2 ∨ gen = 5) then
        some [Spec.Ffdh.parameterAttempts bits.toNat, (bits.toNat + 7) / 8,
          Spec.Ffdh.parameterEntropy bits.toNat, 512 * ((bits.toNat + 7) / 8)]
      else none := by
  simp only [Spec.Ffdh.parameterInit, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq, generatorNat gen 2 (by decide), generatorNat gen 5 (by decide), and_assoc]
  rfl

end VG.Proof.Ffdh.Arm
