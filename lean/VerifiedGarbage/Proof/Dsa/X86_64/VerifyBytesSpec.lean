module
public import VerifiedGarbage.Proof.Dsa.X86_64.VerifyCompute

import VerifiedGarbage.Proof.Dsa.X86_64.AcceptedSpec
import VerifiedGarbage.Proof.Bignum.X86_64.CrtSel
import VerifiedGarbage.Proof.Dsa.SizeBounds
import Mathlib.Tactic.Set
import VerifiedGarbage.Proof.Dsa.SignVerify
import VerifiedGarbage.Proof.Dsa.Arithmetic
import VerifiedGarbage.Proof.Bignum.X86_64.CrtExp
import Mathlib.Tactic.Convert

/-! # The verification mask implements the packed DSA verification spec -/

@[expose] public section

namespace VG.Proof.Dsa.X86_64
open VG

def VerifyValues.key (L : ExecutionLayout) (data : VerifyValues) : Spec.Dsa.Key :=
  ⟨⟨L.modulus, L.subgroup, Spec.Dsa.decodeBE data.generator⟩, Spec.Dsa.decodeBE data.publicValue, none⟩

theorem verifyValue_compute (L : ExecutionLayout) (data : VerifyValues) (digest : List Byte) (n : Nat)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.verify (data.key L) ⟨Spec.Dsa.decodeBE data.signatureR, Spec.Dsa.decodeBE data.signatureS⟩ digest =
      if !Spec.Dsa.keyValid (data.key L) ||
          !(0 < Spec.Dsa.decodeBE data.signatureR && Spec.Dsa.decodeBE data.signatureR < L.subgroup &&
            0 < Spec.Dsa.decodeBE data.signatureS && Spec.Dsa.decodeBE data.signatureS < L.subgroup) then false else
        data.value L == Spec.Dsa.decodeBE data.signatureR := by
  have h := VG.Proof.Dsa.verify_reduced (data.key L)
    ⟨Spec.Dsa.decodeBE data.signatureR, Spec.Dsa.decodeBE data.signatureS⟩ digest n hq
  simp only [VerifyValues.key, VerifyValues.value, VG.Proof.Dsa.powMod_rsa, hz] at h ⊢
  convert h using 1
  congr 1

theorem verifyBytes_compute (L : ExecutionLayout) (data : VerifyValues) (key signature digest : List Byte) (n : Nat)
    (hsize : Spec.Dsa.supportedSizes (Spec.Dsa.bitLength L.modulus) (Spec.Dsa.bitLength L.subgroup))
    (hop : L.modulus % 2 = 1) (hoq : L.subgroup % 2 = 1) (hqf : L.subgroup ≤ 256 ^ L.qLen)
    (hrl : data.signatureR.length = L.qLen) (hkl : key.length = 3 * L.pLen + L.qLen)
    (hsl : signature.length = 2 * L.qLen)
    (hk : Spec.Dsa.publicKeyBytes L.pLen L.qLen key = data.key L)
    (hr : signature.take L.qLen = data.signatureR) (hs : signature.drop L.qLen = data.signatureS)
    (hq : Spec.Dsa.bitLength L.subgroup = 8 * n) (hz : data.digest = digest.take n) :
    Spec.Dsa.verifyBytes L.pLen L.qLen key signature digest = verifyAccepted L data true := by
  have hqpos : 0 < L.subgroup := by have := (VG.Proof.Dsa.supported_bounds hsize).2.1; omega
  rw [verifyAccepted_value L data true hqpos hqf hrl,
    publicAccepted_spec L data.generator data.publicValue hsize hop hoq]
  unfold Spec.Dsa.verifyBytes
  simp only [L.lengths, decide_true, Bool.not_true, hkl, hsl, bne_self_eq_false,
    Bool.false_or, Bool.false_eq_true, ↓reduceIte, hk, hr, hs]
  rw [verifyValue_compute L data digest n hq hz]
  cases hv : Spec.Dsa.keyValid (data.key L) <;>
    by_cases hrange : 0 < Spec.Dsa.decodeBE data.signatureR ∧ Spec.Dsa.decodeBE data.signatureR < L.subgroup <;>
    by_cases srange : 0 < Spec.Dsa.decodeBE data.signatureS ∧ Spec.Dsa.decodeBE data.signatureS < L.subgroup <;>
    by_cases he : data.value L = Spec.Dsa.decodeBE data.signatureR <;>
    simp_all [VerifyValues.key, ← Bool.decide_and, and_assoc] <;>
    first
      | exact decide_eq_decide.mpr Iff.rfl
      | intro h₁ h₂
        first
          | exact absurd h₂ (Nat.not_lt.mpr (srange h₁))
          | exact absurd h₂ (Nat.not_lt.mpr (hrange h₁))

end VG.Proof.Dsa.X86_64
