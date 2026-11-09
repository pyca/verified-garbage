module

public import VerifiedGarbage.Proof.Framework.Bswap

/-!
# GHASH: byte reversal of 64-bit halves

The GHASH implementations load the big-endian halves of a block with a byte
reversal (`bswap`, `rev`), and store them back with another: `byteRev64` is an
involution.
-/

@[expose] public section

namespace VG.Proof.Gcm

theorem getLsbD_byteRev64 (a : BitVec 64) (i : Nat) (hi : i < 64) :
    (byteRev64 a).getLsbD i = a.getLsbD (8 * (7 - i / 8) + i % 8) :=
  VG.byteRev64_getLsbD a hi

theorem byteRev64_byteRev64 (a : BitVec 64) : byteRev64 (byteRev64 a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [getLsbD_byteRev64 _ _ hi, getLsbD_byteRev64 _ _ (by omega)]
  congr 1; omega

end VG.Proof.Gcm
