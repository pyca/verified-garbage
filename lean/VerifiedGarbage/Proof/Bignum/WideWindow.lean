module

public import VerifiedGarbage.Proof.Mont.Words32

/-! # A changed multiplication window contributes at its radix offset -/

@[expose] public section
namespace VG.Proof.Bignum
open VG VG.Proof.Mont

theorem val32_window_add {m m' : Mem} {base : Addr} {out i width tail delta : Nat}
    (O : Outside base (out + 4 * i) (4 * width) m m')
    (bound : out + 4 * (i + width + tail) ≤ 2 ^ 64)
    (V : val32 m' base (out + 4 * i) width = val32 m base (out + 4 * i) width + delta) :
    val32 m' base out (i + width + tail) =
      val32 m base out (i + width + tail) + 2 ^ (32 * i) * delta := by
  have low := O.val32 (d := out) (k := i) (by omega) (by omega)
  have high := O.val32 (d := out + 4 * i + 4 * width) (k := tail) (by omega) (by omega)
  rw [show i + width + tail = i + (width + tail) by omega,
    val32_append, val32_append m, val32_append m' base (out + 4 * i),
    val32_append m base (out + 4 * i), low, V, high]
  simp only [Nat.mul_add]
  omega

end VG.Proof.Bignum
