module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Set only the top bit of an otherwise zero packed-word array. -/

@[expose] public section
namespace VG.Proof.Bignum.Arm
open VG VG.Proof.Mont

theorem val32_write_top_of_zero (m : Mem) (base : Addr) {d n : Nat} (hn : 0 < n)
    (fit : d + 4 * n < 2 ^ 64) (zero : val32 m base d n = 0) (v : BitVec 32) :
    val32 (m.writeW (off base (d + 4 * (n - 1))) v) base d n =
      2 ^ (32 * (n - 1)) * v.toNat := by
  have split : n = (n - 1) + 1 := by omega
  have low : val32 m base d (n - 1) = 0 := by
    rw [split, val32_succ] at zero
    omega
  have outside := writeW32_outside m base (d := d + 4 * (n - 1)) v (by omega)
  calc
    _ = val32 (m.writeW (off base (d + 4 * (n - 1))) v) base d ((n - 1) + 1) := congrArg _ split
    _ = _ := by rw [val32_succ, w32_write_self,
    outside.val32 (d := d) (k := n - 1) (by omega) (by omega), low, Nat.zero_add]

theorem val32_write_top_bit (m : Mem) (base : Addr) {d w : Nat} (hw : 0 < w)
    (fit : d + 8 * w < 2 ^ 64) (zero : val32 m base d (2 * w) = 0) :
    val32 (m.writeW (off base (d + 8 * w - 4)) (0x80000000 : BitVec 32)) base d (2 * w) =
      2 ^ (64 * w - 1) := by
  have address : d + 8 * w - 4 = d + 4 * (2 * w - 1) := by omega
  rw [address, val32_write_top_of_zero m base (by omega) (by omega) zero]
  change 2 ^ (32 * (2 * w - 1)) * 2 ^ 31 = _
  rw [← Nat.pow_add]
  congr 1
  omega

end VG.Proof.Bignum.Arm
