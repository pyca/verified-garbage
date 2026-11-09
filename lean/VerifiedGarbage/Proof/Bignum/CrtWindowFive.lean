module
public import VerifiedGarbage.Proof.Framework.PowLit

import VerifiedGarbage.Proof.Framework.InstancePriority
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! Arithmetic for extracting eight five-bit windows from a group of five
big-endian exponent bytes. No padding bits are added to the exponent. -/

@[expose] public section

namespace VG.Proof.Bignum.CrtWindowFive

/-- A partial final window selects a valid table entry without appending
zero bits to the exponent. -/
theorem pending_index {v b : Nat} (hv : v < 2 ^ b) (hb : b < 5) : v < 32 := by
  have hpow : 2 ^ b ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- Reconstruct the low `n + 1` base-32 digits after consuming the high one. -/
theorem group_reconstruct (E V n : Nat) :
    (32 * E + V / 2 ^ (5 * n) % 32) * 32 ^ n + V % 32 ^ n =
      E * 32 ^ (n + 1) + V % 32 ^ (n + 1) := by
  have hp : 2 ^ (5 * n) = 32 ^ n := by rw [Nat.pow_mul]
  rw [hp, Nat.mod_pow_succ, Nat.pow_succ]
  grind

end VG.Proof.Bignum.CrtWindowFive
