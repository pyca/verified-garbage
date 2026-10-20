module
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Dsa.Digest
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # The native leading-byte test is the p-candidate bit-length guard -/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- An odd shaped X reduces to a positive p no larger than X. -/
theorem pReduction_le {x q : Nat} (hx : x % 2 = 1) :
    0 < x + 1 - x % (2 * q) ∧ x + 1 - x % (2 * q) ≤ x := by
  have hm : x % (2 * q) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by exact ⟨q, rfl⟩), hx]
  have hsub := Nat.mod_le x (2 * q)
  omega

/-- For a fixed-width encoding, the first octet's high bit is exactly the
lower bound used by DSA's p search. -/
theorem candidate_firstByte {len p : Nat} (hl : 0 < len) (hp : p < 256 ^ len) :
    ((Spec.Dsa.encodeBE len p).getD 0 0).toNat < 128 ↔ p < 2 ^ (8 * len - 1) := by
  have he : 256 ^ len = 256 * 256 ^ (len - 1) := by
    rw [show len = (len - 1) + 1 by omega, Nat.pow_succ', Nat.add_sub_cancel]
  have hpow : 0 < 256 ^ (len - 1) := Nat.pow_pos (by decide)
  have hdiv : p / 256 ^ (len - 1) < 256 := (Nat.div_lt_iff_lt_mul hpow).mpr (by omega)
  have hbit : 128 * 256 ^ (len - 1) = 2 ^ (8 * len - 1) := by
    change 2 ^ 7 * (2 ^ 8) ^ (len - 1) = _
    rw [← Nat.pow_mul, ← Nat.pow_add]
    congr 1
    omega
  simp only [VG.Proof.Dsa.encodeBE_i2osp, Spec.Rsa.i2osp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hl, Option.map_some, Option.getD_some, Nat.sub_zero, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt hdiv, Nat.div_lt_iff_lt_mul hpow, hbit]

end VG.Proof.Dsa.Generation
