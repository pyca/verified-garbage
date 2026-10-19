module
public import VerifiedGarbage.Spec.Rsa.Mont
public import Batteries.Logic
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Bignum.Arm.HeaderBridge

/-! # The padded CRT residue fits the addition loop's input width -/

@[expose] public section

namespace VG.Proof.Bignum.Arm
open VG VG.Arm VG.Proof.Mont
open VG.Spec.Rsa.Mont (numAt arrAt)

theorem val32_prefix_of_eq {m : Mem} {base : Addr} {d n k value : Nat}
    (h : val32 m base d (n + k) = value) (fit : value < 2 ^ (32 * n)) :
    val32 m base d n = value := by
  have eq := congrArg (fun x => x % 2 ^ (32 * n)) h
  rw [val32_append] at eq
  simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
    Nat.add_zero, Nat.mod_eq_of_lt (val32_lt m base d n), Nat.mod_eq_of_lt fit] using eq

theorem crt_paddedResidue_low {m before : Mem} {base : Addr} {d w o : Nat}
    (h : val32 m base d (4 * w + 2) = numAt before base w o) :
    val32 m base d (4 * w) = numAt before base w o := by
  apply val32_prefix_of_eq h
  rw [numAt_native]
  exact Nat.lt_of_lt_of_le (val32_lt before base (arrAt w o) (2 * w))
    (Nat.pow_le_pow_right (by decide) (by omega))

end VG.Proof.Bignum.Arm
