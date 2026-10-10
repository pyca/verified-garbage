import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Mem

/-!
# Addresses at offsets, for the modes

Facts about the bytes at offsets of a base address that the modes'
proofs share, on any 64-bit target. Nothing here depends on a cipher or a
target.
-/

namespace VG.Proof.Modes

open VG

theorem off_sub_toNat (B : Addr) {t e : Nat} (h : e ≤ t) (ht : t < 2 ^ 64) :
    (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat = t - e := by
  rw [VG.Offset.add_sub_add _ h, BitVec.toNat_ofNat]; omega

theorem off_sub_not (B : Addr) {t e n : Nat} (h : t < e ∨ e + n ≤ t) (ht : t < 2 ^ 64) (hn : 0 < n)
    (he : e + n ≤ 2 ^ 64) : ¬ (B + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < n := by
  rw [VG.Offset.add_sub_add_left]; exact VG.Offset.not_lt_sub_ofNat h ht hn he

/-- A byte of `A`'s area is not among the 8 at `B + e`. -/
theorem not_in_of_disjoint {A B : Addr} {n t e : Nat} (hsep : Region.Disjoint ⟨A, n⟩ ⟨B, n⟩) (ht : t < n)
    (he : e + 8 ≤ n) (hn : n < 2 ^ 64) : ¬ (A + BitVec.ofNat 64 t - (B + BitVec.ofNat 64 e)).toNat < 8 :=
  fun h => hsep (A + BitVec.ofNat 64 t) (VG.Offset.contains_base A (by omega) (by omega))
    (VG.Offset.sub_base B he _ (by simp only [Region.Contains]; omega))

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

end VG.Proof.Modes
