module

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge
public import Init.Prelude
public import VerifiedGarbage.Proof.Mont.Words32
public import VerifiedGarbage.Spec.Rsa.Mont
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
import VerifiedGarbage.Proof.Framework.Offset

/-! A single word in a zeroed array represents one radix power. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont
open VG.Spec.Rsa.Mont (arrAt numAt)

theorem val32_zero_parts {m : Mem} {base : Addr} {d j k : Nat}
    (zero : val32 m base d (j + k) = 0) :
    val32 m base d j = 0 ∧ val32 m base (d + 4 * j) k = 0 := by
  rw [val32_append] at zero
  have firstZero : val32 m base d j = 0 := by omega
  have prod : 2 ^ (32 * j) * val32 m base (d + 4 * j) k = 0 := by omega
  exact ⟨firstZero, (Nat.mul_eq_zero.mp prod).resolve_left (Nat.ne_of_gt (Nat.pow_pos (by decide)))⟩

theorem normalizedSeed_value (m : Mem) (base : Addr) {w : Nat}
    (hw : 2 ≤ w) (fit : base.toNat + (arrAt w 4 + 8 * w) ≤ 2 ^ 32)
    (zero : numAt m base w 4 = 0) :
    numAt (m.writeW (off base (arrAt w 4 + 8 * (w - 1))) (1#32)) base w 4 =
      2 ^ (64 * (w - 1)) := by
  let d := arrAt w 4
  let j := 2 * (w - 1)
  let tail := 2 * w - (j + 1)
  have split : 2 * w = j + (1 + tail) := by dsimp [j, tail]; omega
  rw [numAt_native] at zero ⊢
  change val32 (m.writeW (off base (d + 8 * (w - 1))) (1#32)) base d (2 * w) = _
  have offset : 8 * (w - 1) = 4 * j := by dsimp [j]; omega
  rw [offset]
  have zeros := val32_zero_parts (j := j) (k := 1 + tail) (by simpa only [← split] using zero)
  have zeros' := val32_zero_parts (j := 1) (k := tail) zeros.2
  have outside := writeW32_outside m base (d := d + 4 * j) (1#32) (by dsimp [d, j] at *; omega)
  rw [split, val32_append, outside.val32 (by left; omega) (by dsimp [d, j] at *; omega), zeros.1]
  rw [Nat.zero_add, show 1 + tail = tail + 1 by omega, val32,
    w32_write_self, outside.val32 (by right; omega) (by dsimp [d, j, tail] at *; omega)]
  have ztail : val32 m base (d + 4 * j + 4) tail = 0 := by simpa only [Nat.mul_one] using zeros'.2
  rw [ztail]
  simp only [BitVec.toNat_ofNat, Nat.mul_zero, Nat.add_zero]
  change 2 ^ (32 * j) * 1 = 2 ^ (64 * (w - 1))
  rw [Nat.mul_one]
  congr 1
  dsimp [j]
  omega

end VG.Proof.Bignum.Arm
