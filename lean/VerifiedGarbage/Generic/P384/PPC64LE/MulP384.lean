module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P384.MulLit

/-!
# P-384's point multiplication on PPC64LE

`vg_p384_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.PPC64LE.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact PPC64LE.target {
    notes := ["The function keeps `r31` and `lr` in bytes 2224 to 2239 of `ws` (in `r3`, which \
      it keeps) while it runs, and writes no other callee-saved register. It expands `k` into a \
      table of its bits, one per byte, at bytes 4096 to 4479, copies `Q` to bytes 1456 to 1551 (slots 29 \
      and 30), and runs a double-and-add ladder over the 384 bits of `k`'s 48 bytes, from \
      the top, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling (calls of `vg_p384_point_double` and \
      `vg_p384_point_add`) and a masked selection for each bit. Field elements are \
      six 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication in calls of `vg_p384_mul_mod_p` and the other functions of `p384_mont`; \
      nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.PPC64LE.mulP384
    verified := Proof.Ecdsa.PPC64LE.P384.Mul.mul_verified h.law }]

end VG.Generic.P384.PPC64LE.MulP384
