module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CvVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rsa.Arm

def artifacts : List Artifact := [
  Spec.Rsa.publicCheckedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: Montgomery multiplication on 32-bit limbs, two to each 64-bit word \
        of the working space (coarsely integrated operand scanning, each 32 × 32-bit product from \
        four 16 × 16-bit `mul`s, since `umull` is not in the model), the final subtraction \
        selected under a mask. `e` and `n` are checked first; then R² mod n by constant-time \
        doublings, and binary exponentiation. The input's range check gives a mask: an input \
        out of range takes the same arithmetic, and the output is cleared under the mask."]
    code := Impl.Bignum.Arm.PublicFn.code
    stack := 56
    verified := Proof.Bignum.Arm.public_verified },
  Spec.Rsa.publicPrecomputeApi.artifact Arm.target {
    notes := ["Baseline ARMv7: `n` is checked and read into 32-bit limbs, its 64-bit Montgomery \
        inverse computed from pairs of them, and R² mod n by a fixed number of modular \
        doublings. The output is cleared for an invalid modulus."]
    code := Impl.Bignum.Arm.PcFn.code
    stack := 56
    verified := Proof.Bignum.Arm.precompute_verified },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact Arm.target {
    notes := ["Baseline ARMv7: `pre` is read and checked (`n` odd, its top word not zero, \
        `R² mod n` below it) before any arithmetic, so that values of no modulus are safe; then \
        `vg_rsa_public_checked`'s Montgomery inverse and exponentiation. The input's acceptance \
        and the clearing of the output are under masks."]
    code := Impl.Bignum.Arm.PdFn.code
    stack := 56
    verified := Proof.Bignum.Arm.pd_verified },
  Spec.Rsa.privateCrtApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the checks of the input and the key give a mask; rejected primes \
        are replaced, so that the arithmetic is the same whatever the key, and a rejected result \
        is cleared under the mask. Each prime's working space at the width of `n` reduces the \
        input modulo the prime by two Montgomery products; a narrow working space then takes the \
        prime, its own Montgomery constants and the reduced input at the prime's width \
        (`max(2, ⌈len/8⌉)` limbs of 64 bits for its public length), where the exponentiation \
        follows a fixed schedule over 32-bit limbs. `qInv` is reduced as a signed coefficient \
        and the result recombined in a double-width product, at the width of `n`."]
    code := Impl.Bignum.Arm.CrtFn.code
    stack := 56
    verified := Proof.Bignum.Arm.crt_verified },
  Spec.Rsa.crtValuesApi.artifact Arm.target {
    notes := ["Baseline ARMv7, frameless (the callee-saved registers are kept in the working \
        space): `n` is checked first, the only branch on data. `n`, `p`, `q` and `d` are read into \
        32-bit limbs at the width of `n`, and `n` divided by `p` by a fixed-iteration long \
        division. `q⁻¹ mod (p | 1)` and the gcd come from a binary extended Euclidean algorithm of \
        a fixed number of steps, whose subtractions and halvings are selected under masks. \
        `p` odd, `n / p = q`, `n mod p = 0` and a gcd of 1 make a mask; `dP` and `dQ` are \
        `d mod (p - 1)` and `d mod (q - 1)` by the same division, and the three results are \
        written out under the mask, cleared if it is not set."]
    code := Impl.Rsa.Arm.CrtValues.code
    stack := 0
    verified := Proof.Rsa.Arm.CrtValues.crt_values_verified }]

end VG.Artifacts.Rsa.Arm
