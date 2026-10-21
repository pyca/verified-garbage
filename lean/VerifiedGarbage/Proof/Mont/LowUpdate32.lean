module

public import VerifiedGarbage.Proof.Mont.Words32
import VerifiedGarbage.Proof.Rsa.KeyBits32

/-! # Native low-word updates and restoration preserve the higher integer -/

@[expose] public section
namespace VG.Proof.Mont
open VG

theorem val32_low_or_one {m m' : Mem} {base : Addr} {src n : Nat} (positive : 0 < n)
    (fit : src + 4 * n ≤ 2 ^ 64) (O : Outside base src 4 m m')
    (low : w32 m' base src = w32 m base src ||| 1) :
    val32 m' base src n = val32 m base src n + (1 - val32 m base src n % 2) := by
  rw [show n = n - 1 + 1 by omega, val32, val32, low,
    O.val32 (d := src + 4) (k := n - 1) (by omega) (by omega), VG.Proof.Rsa.KeyBits32.or_one]
  omega

theorem val32_restore_low {m m' : Mem} {base : Addr} {src n : Nat} (positive : 0 < n)
    (fit : src + 4 * n ≤ 2 ^ 64) (O : Outside base src 4 m m')
    (low : w32 m' base src = w32 m base src) : val32 m' base src n = val32 m base src n := by
  rw [show n = n - 1 + 1 by omega, val32, val32, low,
    O.val32 (d := src + 4) (k := n - 1) (by omega) (by omega)]

end VG.Proof.Mont
