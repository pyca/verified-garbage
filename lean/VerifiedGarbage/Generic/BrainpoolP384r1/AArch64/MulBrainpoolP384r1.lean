module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP384r1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP384r1's point multiplication on AArch64

`vg_brainpoolp384r1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP384r1's group law and inversions `h`, the variant
`Variants/BrainpoolP384r1/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`brainpoolp384r1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP384r1.AArch64.MulBrainpoolP384r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP384r1.Mul

/-- What the function runs. -/
def note : String :=
  "The function keeps `x19` in bytes 2608 to 2615 of `ws` while it runs, expands `k` into a \
  table of its bits, one per byte, at bytes 2224 to 2607, copies `Q` to bytes 1456 to 1551 \
  (slots 29 and 30), and runs a ladder over the 384 bits of `k`'s six words, from the top: \
  each step doubles the accumulator and adds `Q` by the general complete addition formulas of \
  Renes, Costello and Batina (Algorithm 1, with `a` and `3 b` read from `ws`), and keeps the sum \
  or the double by a mask of the bit. Field elements are six 64-bit words in Montgomery form, \
  multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`) with a \
  final conditional subtraction, its temporary area at bytes 4048 to 4095; nothing depends on \
  `k` or `Q` but through masks. It writes no vector register."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP384r1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      notes := [note]
      code := brainpoolp384r1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.BrainpoolP384r1.AArch64.MulBrainpoolP384r1
