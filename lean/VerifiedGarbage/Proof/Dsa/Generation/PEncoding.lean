module
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.PlainSimp
public import VerifiedGarbage.Spec.Dsa

import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Dsa.Encoding
import VerifiedGarbage.Proof.Dsa.Digest

/-! # Assemble the hash contributions for a DSA p candidate

Hashes are stored most significant contribution first. The shared shaper
then keeps the requested low bits and sets the top bit. Its low-bit write
does not change the following even-modulus reduction.
-/

@[expose] public section
namespace VG.Proof.Dsa.Generation
open VG

/-- Joining a high radix digit to a bounded low part commutes with cutting
the high digit. This is the truncation of p's final hash contribution. -/
theorem radix_join_mod {lo base : Nat} (hlo : lo < base) (hi cut : Nat) :
    (lo + hi * base) % (base * cut) = lo + (hi % cut) * base := by
  rw [Nat.mod_mul]
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlo, Nat.add_mul_div_right _ _ (by omega),
    Nat.div_eq_of_lt hlo, Nat.zero_add]
  rw [Nat.mul_comm]

/-- Appending a digest at the most significant end appends a radix digit. -/
theorem prepend_digest (digest low : List Byte) :
    Spec.Dsa.decodeBE (digest ++ low) =
      Spec.Dsa.decodeBE low + Spec.Dsa.decodeBE digest * 256 ^ low.length := by
  rw [decodeBE_append, Nat.add_comm]

/-- A fixed-width byte copy with zero carry preserves the seed exactly. -/
theorem seedAdd_zero (bs : List Byte) :
    Spec.Dsa.encodeBE bs.length (Spec.Dsa.decodeBE bs + 0) = bs := by
  rw [Nat.add_zero, encodeBE_decodeBE]

end VG.Proof.Dsa.Generation
