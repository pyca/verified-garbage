module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P521.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P521.MulLit

/-!
# P-521's point multiplication on 32-bit ARM

`vg_p521_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-521's group law `h`, the variant
`Variants/P521/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P521.Arm.MulP521

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P521.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p521.mulApi.artifact Arm.target {
    notes := ["The function keeps `r4`–`r9`, `r11` and `lr` in bytes 3304 to 3339 of `ws` and \
      `r10` in `lr` while it runs, expands `k` into a table of its bits, one per byte, at bytes \
      4096 to 4671, copies `Q` to bytes 2152 to 2295 (slots 29 and 30), and runs a double-and-add \
      ladder over the 528 bits of `k`'s 66 bytes, from the top, with the complete \
      addition formulas of Renes, Costello and Batina for every addition and doubling \
      (inline, with `a` and `3 b` read from `ws`) and a masked selection for each \
      bit. Field elements are eighteen packed 32-bit words in Montgomery form, multiplied by \
      packed-word Montgomery multiplication in calls of `vg_p521_mul_mod_p` and the other functions of \
      `p521_mont`; nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.Arm.mulP521
    verified := Proof.Ecdsa.Arm.P521.Mul.mul_verified h.law }]

end VG.Generic.P521.Arm.MulP521
