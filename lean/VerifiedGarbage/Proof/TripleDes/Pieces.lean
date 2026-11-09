module

public import VerifiedGarbage.Spec.TripleDes
public import VerifiedGarbage.Proof.Framework.Bitslice.Table
import VerifiedGarbage.Proof.TripleDes.Permutation
import VerifiedGarbage.Proof.TripleDes.Round

/-!
# A DES round, one S-box at a time

The code of every target that runs the S-boxes one at a time (on PPC64LE
and RISC-V) forms the six input bits of S-box `i` (`roundChunk i`, of E of R
XORed with the round key): `roundChunk_bit` gives each of them as a bit of R
and of the round key. Untrusted.
-/

@[expose] public section

namespace VG.Proof.TripleDes

open VG.Bitslice VG.Spec.TripleDes

def roundChunk (i : Nat) (r : BitVec 32) (k : BitVec 48) : BitVec 6 :=
  ((permute expansion r ^^^ k) >>> (6 * (7 - i))).setWidth 6

theorem roundChunk_bit (i j : Nat) (hi : i < 8) (hj : j < 6)
    (r : BitVec 64) (k : BitVec 64) :
    (roundChunk i (r.setWidth 32) (k.setWidth 48)).getLsbD j =
      (r.getLsbD (32 - expansion.getD (6 * i + 5 - j) 1) ^^
        k.getLsbD (47 - (6 * i + 5 - j))) := by
  have ht : 6 * (7 - i) + j < 48 := by omega
  have heq : 48 - 1 - (6 * (7 - i) + j) = 6 * i + 5 - j := by omega
  have hkey : 6 * (7 - i) + j = 47 - (6 * i + 5 - j) := by omega
  have hsource : 32 - expansion.getD (6 * i + 5 - j) 1 < 32 := by
    have hb : ∀ t < 48, 1 ≤ expansion.getD t 1 := by decide +kernel
    have hpos : 6 * i + 5 - j < 48 := by omega
    have := hb _ hpos
    omega
  simp only [roundChunk, BitVec.getLsbD_setWidth, hj, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor]
  rw [permute_bit _ _ (by decide) _ ht]
  rw [heq]
  simp only [BitVec.getLsbD_setWidth, hsource, ht, decide_true, Bool.true_and]
  rw [hkey]

end VG.Proof.TripleDes
