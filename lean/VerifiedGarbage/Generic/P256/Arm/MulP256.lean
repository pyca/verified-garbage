module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P256.MulLit

public import VerifiedGarbage.Proof.Ecdsa.Arm.P256.Umaal

/-!
# P-256's point multiplication on 32-bit ARM

`vg_p256_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-256's group law `h`, the variant
`Variants/P256/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P256.Arm.MulP256

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P256.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p256.mulApi.artifact Arm.target {
    notes := ["The function keeps `r4`–`r9`, `r11` and `lr` in bytes 1504 to 1539 of `ws` and \
      `r10` in `lr` while it runs, expands `k` into a table of its bits, one per byte, at bytes \
      4096 to 4351, copies `Q` to bytes 992 to 1055 (slots 29 and 30), and runs a double-and-add \
      ladder over the 256 bits of `k`'s 32 bytes, from the top, with the complete \
      addition formulas of Renes, Costello and Batina for every addition and doubling \
      (calls of `vg_p256_point_double` and \
      `vg_p256_point_add`, with `a` and `3 b` read from `ws`) and a masked selection for each \
      bit. Field elements are sixteen 16-bit digits in Montgomery form, multiplied by \
      digit-by-digit Montgomery multiplication in calls of `vg_p256_mul_mod_p` and the other functions of \
      `p256_mont`; nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.Arm.mulP256
    verified := Proof.Ecdsa.Arm.P256.Mul.mul_verified h.law },
  Spec.Weierstrass.Mul.p256.mulApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["`vg_p256_mul`'s code, but for its calls of `vg_p256_point_double_umaal` and \
      `vg_p256_point_add_umaal`. Field multiplications are calls of `vg_p256_mul_mod_p_umaal` (and `vg_p256_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Impl.Ecdsa.Arm.mulP256U
    verified := Proof.Ecdsa.Arm.P256.Mul.mulU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P256.Arm.MulP256
