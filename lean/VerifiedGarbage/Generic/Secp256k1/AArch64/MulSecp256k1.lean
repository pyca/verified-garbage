module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Secp256k1.MulVerified
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# secp256k1's point multiplication on AArch64

`vg_secp256k1_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over secp256k1's group law and inversions `h`, the variant
`Variants/Secp256k1/AArch64/Law.lean`: the ladder's proof takes the group law,
and the curve's facts (`secp256k1_ok`) its inversions.
-/

@[expose] public section

namespace VG.Generic.Secp256k1.AArch64.MulSecp256k1

open VG.Impl.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.Secp256k1.Mul

/-- What the function runs. -/
def note : String :=
  "The function keeps `x19` in bytes 1760 to 1767 of `ws` while it runs, expands `k` into a \
  table of its bits, one per byte, at bytes 1504 to 1759, copies `Q` to bytes 992 to 1055 \
  (slots 29 and 30), and runs a ladder over the 256 bits of `k`'s four words, from the top: \
  each step doubles the accumulator and adds `Q` by the general complete addition formulas of \
  Renes, Costello and Batina (Algorithm 1, with `a` and `3 b` read from `ws`), and keeps the sum \
  or the double by a mask of the bit. Field elements are four 64-bit words in Montgomery form, \
  multiplied by word-by-word Montgomery multiplication (CIOS, with `mul` and `umulh`) with a \
  final conditional subtraction; nothing depends on `k` or `Q` but through masks. It writes no \
  vector register."

def artifacts (h : Proof.Weierstrass.AArch64.HasLawInv Spec.Secp256k1.curve) : List Artifact :=
  [C.mulApi.artifact AArch64.target {
      notes := [note]
      code := secp256k1.mulFn
      verified := mul_verified h.law h.inv }]

end VG.Generic.Secp256k1.AArch64.MulSecp256k1
