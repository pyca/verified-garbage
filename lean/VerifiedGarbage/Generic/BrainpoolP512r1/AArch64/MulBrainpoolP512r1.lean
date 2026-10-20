module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.BrainpoolP512r1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# brainpoolP512r1's point multiplication on AArch64

`vg_brainpoolp512r1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over brainpoolP512r1's group law and inversions `h`, the variant
`Variants/BrainpoolP512r1/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`brainpoolp512r1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.BrainpoolP512r1.AArch64.MulBrainpoolP512r1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.BrainpoolP512r1.Mul

/-- What the function runs. -/
def note : String :=
  "The function keeps `x19` and `x21`–`x25` in bytes 3456 to 3503 of `ws` while it runs, expands \
  `k` into a table of its bits, one per byte, at bytes 2944 to 3455, copies `Q` to bytes 1920 to 2047 \
  (slots 29 and 30), and runs a ladder over the 512 bits of `k`'s eight words, from the top: \
  each step doubles the accumulator and adds `Q` by the general complete addition formulas of \
  Renes, Costello and Batina (Algorithm 1, with `a` and `3 b` read from `ws`), and keeps the sum \
  or the double by a mask of the bit. Field elements are eight 64-bit words in Montgomery form, \
  multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`) with a \
  final conditional subtraction, its temporary area at bytes 192 to 255; nothing depends on \
  `k` or `Q` but through masks. It writes no vector register."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.BrainpoolP512r1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      notes := [note]
      code := brainpoolp512r1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.BrainpoolP512r1.AArch64.MulBrainpoolP512r1
