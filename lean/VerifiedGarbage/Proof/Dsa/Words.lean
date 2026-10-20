module

public import VerifiedGarbage.Proof.Bignum.Words
import VerifiedGarbage.Proof.Framework.Omega

/-! # Small-value predicates on padded DSA limb arrays -/

@[expose] public section

namespace VG.Proof.Dsa
open VG VG.Proof.Bignum

/-- A small value occupies only the first limb, regardless of padding. -/
theorem words_eq_small {mem : Mem} {B : Addr} {d w value : Nat}
    (hw : 1 ≤ w) (hv : value < 2 ^ 64) :
    wv mem B d w = value ↔ (word mem B d).toNat = value ∧
      ∀ i, 1 ≤ i → i < w → word mem B (d + 8 * i) = 0 := by
  have split := wv_add mem B d 1 (w - 1)
  rw [show 1 + (w - 1) = w by omega] at split
  have first : wv mem B d 1 = (word mem B d).toNat := by simp [wv]
  rw [split, first]
  have tailZero := wv_eq_zero_iff mem B (d + 8 * 1) (w - 1)
  constructor
  · intro h
    have ht : wv mem B (d + 8 * 1) (w - 1) = 0 := by
      change (word mem B d).toNat + 2 ^ 64 * wv mem B (d + 8 * 1) (w - 1) = value at h
      omega
    refine ⟨by rw [ht, Nat.mul_zero, Nat.add_zero] at h; exact h, fun i hi1 hi => ?_⟩
    have he := tailZero.mp ht (i - 1) (by omega)
    rwa [show d + 8 * 1 + 8 * (i - 1) = d + 8 * i by omega] at he
  · rintro ⟨hfirst, hhigh⟩
    have ht : wv mem B (d + 8 * 1) (w - 1) = 0 := tailZero.mpr fun i hi => by
      rw [show d + 8 * 1 + 8 * i = d + 8 * (i + 1) by omega]
      exact hhigh (i + 1) (by omega) (by omega)
    rw [ht, Nat.mul_zero, Nat.add_zero, hfirst]

/-- XORing the first limb with one and ORing the rest tests exactly one. -/
theorem words_eq_one {mem : Mem} {B : Addr} {d w : Nat} (hw : 1 ≤ w) :
    ((word mem B d ^^^ 1) = 0 ∧ ∀ i, 1 ≤ i → i < w → word mem B (d + 8 * i) = 0) ↔
      wv mem B d w = 1 := by
  rw [words_eq_small hw (by decide)]
  apply and_congr _ Iff.rfl
  change (word mem B d ^^^ 1#64) = 0#64 ↔ _
  rw [BitVec.xor_eq_zero_iff]
  exact ⟨fun h => congrArg BitVec.toNat h, fun h => BitVec.eq_of_toNat_eq h⟩

end VG.Proof.Dsa
