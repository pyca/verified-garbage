module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P224.MulLit

/-!
# P-224's point multiplication on 32-bit ARM

`vg_p224_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-224's group law `h`, the variant
`Variants/P224/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P224.Arm.MulP224

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P224.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p224.mulApi.artifact Arm.target {
    notes := ["The function keeps `r4`–`r9`, `r11` and `lr` in bytes 1504 to 1539 of `ws` and \
      `r10` in `lr` while it runs, expands `k` into a table of its bits, one per byte, at bytes \
      4096 to 4351, copies `Q` to bytes 992 to 1055 (slots 29 and 30), and runs a double-and-add \
      ladder over the 224 bits of `k`'s 28 bytes, from the top, with the complete \
      addition formulas of Renes, Costello and Batina for every addition and doubling \
      (calls of `vg_p224_point_double` and \
      `vg_p224_point_add`, with `a` and `3 b` read from `ws`) and a masked selection for each \
      bit. Field elements are sixteen 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication in calls of `vg_p224_mul_mod_p` and the other functions of \
      `p224_mont`; nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.Arm.mulP224
    verified := Proof.Ecdsa.Arm.P224.Mul.mul_verified h.law }]

end VG.Generic.P224.Arm.MulP224
