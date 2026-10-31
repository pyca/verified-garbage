module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.Proof.Weierstrass.Law
public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Ecdsa.Arm.P384.MulLit

public import VerifiedGarbage.Proof.Ecdsa.Arm.P384.Umaal

/-!
# P-384's point multiplication on 32-bit ARM

`vg_p384_mul` (`Spec/Weierstrass/Mul.lean`), which the signature, the
public key derivation, verification and ECDH call. A generic file (see
`TCB/Emit.lean`) over P-384's group law `h`, the variant
`Variants/P384/Arm/Law.lean`.
-/

@[expose] public section

namespace VG.Generic.P384.Arm.MulP384

def artifacts (h : Proof.Weierstrass.HasLaw Spec.P384.curve) : List Artifact := [
  Spec.Weierstrass.Mul.p384.mulApi.artifact Arm.target {
    notes := ["The function keeps `r4`–`r9`, `r11` and `lr` in bytes 2224 to 2259 of `ws` and \
      `r10` in `lr` while it runs, expands `k` into a table of its bits, one per byte, at bytes \
      4096 to 4479, copies `Q` to bytes 1456 to 1551 (slots 29 and 30), and runs a double-and-add \
      ladder over the 384 bits of `k`'s 48 bytes, from the top, with the complete \
      addition formulas of Renes, Costello and Batina for every addition and doubling \
      (calls of `vg_p384_point_double` and \
      `vg_p384_point_add`, with `a` and `3 b` read from `ws`) and a masked selection for each \
      bit. Field elements are twelve packed 32-bit words in Montgomery form, multiplied by \
      word-by-word Montgomery multiplication in calls of `vg_p384_mul_mod_p` and the other functions of \
      `p384_mont`; nothing depends on `k` or `Q` but through masks."]
    code := Impl.Ecdsa.Arm.mulP384
    verified := Proof.Ecdsa.Arm.P384.Mul.mul_verified h.law },
  Spec.Weierstrass.Mul.p384.mulApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["`vg_p384_mul`'s code, but for its calls of `vg_p384_point_double_umaal` and \
      `vg_p384_point_add_umaal`. Field multiplications are calls of `vg_p384_mul_mod_p_umaal` (and `vg_p384_mul_mod_n_umaal`), which multiply the numbers' 32-bit words with one `umaal` per word of each Montgomery row (`hi:lo = n m + hi + lo`)."]
    code := Impl.Ecdsa.Arm.mulP384U
    verified := Proof.Ecdsa.Arm.P384.Mul.mulU_verified h.law
    features := ["umaal"] }]

end VG.Generic.P384.Arm.MulP384
