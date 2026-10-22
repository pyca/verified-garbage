module

public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Mont
import VerifiedGarbage.Proof.Bignum.ByteWords

/-! # Target-independent extraction of exponent words -/

@[expose] public section
namespace VG.Proof.MillerRabin
open VG VG.Proof.Mont

/-- Word `i` of a number of `k` words. -/
theorem val32_word' (m : Mem) (base : Addr) {d k i : Nat} (hi : i < k) :
    w32 m base (d + 4 * i) = val32 m base d k / 2 ^ (32 * i) % 2 ^ 32 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = i + (r + 1) := ⟨k - i - 1, by omega⟩
  rw [val32_append m base d i (r + 1)]
  simp only [val32]
  have lo := val32_lt m base d i
  have hw : w32 m base (d + 4 * i) < 2 ^ 32 := (m.readW _ 32).isLt
  have hp : 0 < 2 ^ (32 * i) := Nat.two_pow_pos _
  rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt lo, Nat.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hw]

theorem montNum_val32 (m : Mem) (base : Addr) (n j : Nat) :
    Spec.Rsa.Mont.numAt m base n j = val32 m base (Spec.Rsa.Mont.arrAt n j) (2 * n) := by
  unfold Spec.Rsa.Mont.numAt
  change (m.read (off base (Spec.Rsa.Mont.arrAt n j)) (8 * n)).toNat = _
  rw [show 8 * n = 4 * (2 * n) by omega, VG.Proof.Bignum.read_eq_val32]

theorem montNum_low32 (m : Mem) (base : Addr) {n j : Nat} (positive : 0 < n) :
    w32 m base (Spec.Rsa.Mont.arrAt n j) = Spec.Rsa.Mont.numAt m base n j % 2 ^ 32 := by
  rw [montNum_val32]
  simpa only [Nat.mul_zero, Nat.add_zero, Nat.pow_zero, Nat.div_one] using
    (val32_word' m base (d := Spec.Rsa.Mont.arrAt n j) (k := 2 * n) (i := 0) (by omega))

end VG.Proof.MillerRabin
