module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Spec.Rsa

import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyMaskFlag
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyFinalExponent
import VerifiedGarbage.Proof.Rsa.X86.KeyBits
import VerifiedGarbage.Proof.RsaKeyGen.TopWord32
import VerifiedGarbage.Proof.Mont.X86.Instr
/-! # The final native mask is exactly the RSA key shape check -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/KeyTopBit.lean`, which only this module imported.
section


end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Rsa.X86.Keys
open VG.Impl.Rsa.X86.Keys hiding slot
open VG.Impl.RsaKeyGen.X86.Key

theorem mask_bit (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) ≤ 1 := by
  split <;> decide

theorem mask_ite_one (P : Prop) [Decidable P] : (if P then 1 else 0 : Nat) = 1 ↔ P := by
  by_cases H : P <;> simp [H]

/-- The flag the final checks leave, as the conjunction of the checks: a
lemma about numbers, so that `KeyRuntime.finalMask_ok` does not normalize the
condition among facts about memory. -/
theorem finalMask_cond (m k N P Q e : Nat) :
    (if 3 ≤ e ∧ (if (if (if (if (if m = 1 ∧ (if k ≤ N then 1 else 0) = 1 then 1 else 0) = 1 ∧
        P % 2 = 1 then 1 else 0) = 1 ∧ Q % 2 = 1 then 1 else 0) = 1 ∧ e % 2 = 1 then 1 else 0) = 1 ∧
        (if e < 2 ^ 33 then 1 else 0) = 1 then 1 else 0) = 1 then 1 else 0 : Nat) =
      if m = 1 ∧ k ≤ N ∧ P % 2 = 1 ∧ Q % 2 = 1 ∧ Spec.Rsa.exponentValid e = true then 1 else 0 := by
  simp only [mask_ite_one, Spec.Rsa.exponentValid, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    and_assoc, and_comm, and_left_comm]

end VG.Proof.RsaKeyGen.X86.Key
