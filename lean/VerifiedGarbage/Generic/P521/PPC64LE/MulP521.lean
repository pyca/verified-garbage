module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.P521.MulLit

/-!
# P-521's point multiplication on PPC64LE

`vg_p521_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/PPC64LE/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.PPC64LE.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact PPC64LE.target {
    notes := ["The function keeps `r31` and `lr` in bytes 3304 to 3319 of `ws` (in `r3`, which \
      it keeps) while it runs, and writes no other callee-saved register. It expands `k` into a \
      table of its bits, one per byte, at bytes 4096 to 4671, copies `Q` to bytes 2152 to 2295 (slots 29 \
      and 30), and runs a double-and-add ladder over the 528 bits of `k`'s 66 bytes, from \
      the top, with the complete addition formulas of Renes, Costello and Batina for every \
      addition and doubling (inlined, as calls of the field functions: the points do not fit the point \
      functions' slots) and a masked selection for each bit. Field elements are \
      nine 64-bit words in Montgomery form, multiplied by word-by-word Montgomery \
      multiplication in calls of `vg_p521_mul_mod_p` and the other functions of `p521_mont`; \
      nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.PPC64LE.mulP521
    verified := Proof.Ecdsa.PPC64LE.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.PPC64LE.MulP521
