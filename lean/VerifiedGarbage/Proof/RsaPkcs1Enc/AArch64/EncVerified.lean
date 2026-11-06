module

import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCT
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.Callee
public import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncLay
public import VerifiedGarbage.Spec.RsaPkcs1Enc.Contract
import VerifiedGarbage.Proof.RsaPkcs1Enc.AArch64.EncCorrect

/-!
# RSAES-PKCS1-v1_5 encryption on AArch64: the leak of `n` and `e`

The leak of `n` and `e`, the bytes' values, split into the two
(`leak_split`).
-/

@[expose] public section

namespace VG.Proof.RsaPkcs1Enc.AArch64.Enc

open VG VG.AArch64 VG.Impl.RsaPkcs1Enc.AArch64.Encrypt

theorem map_toNat_inj : ∀ {a b : List Byte}, a.map (·.toNat) = b.map (·.toNat) → a = b
  | [], [], _ => rfl
  | x :: a, y :: b, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [BitVec.eq_of_toNat_eq h.1, map_toNat_inj h.2]

/-- The leak of `n` and `e`, split. -/
theorem leak_split {a b c d : List Byte} (h : (a ++ b).map (·.toNat) = (c ++ d).map (·.toNat))
    (hl : a.length = c.length) : a = c ∧ b = d := by
  rw [List.map_append, List.map_append] at h
  obtain ⟨e₁, e₂⟩ := List.append_inj h (by simp only [List.length_map, hl])
  exact ⟨map_toNat_inj e₁, map_toNat_inj e₂⟩

end VG.Proof.RsaPkcs1Enc.AArch64.Enc
