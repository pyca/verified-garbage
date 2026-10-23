module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CvVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CckVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CkVerified
public import VerifiedGarbage.Proof.Rsa.Arm.RvVerified
public import VerifiedGarbage.Proof.Rsa.Arm.FusedVerified
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
        doublings, and binary exponentiation, its squarings by a dedicated Montgomery square \
        (each cross product once, doubled, the words' squares added, then reduced in place). The \
        input's range check gives a mask: an input \
        out of range takes the same arithmetic, and the output is cleared under the mask."]
    code := Impl.Bignum.Arm.PublicFn.code
    stack := 56
    verified := Proof.Bignum.Arm.public_verified },


  Spec.Rsa.privateCrtApi.artifact Arm.target {
    notes := ["Baseline ARMv7: the checks of the input and the key give a mask; rejected primes \
        are replaced, so that the arithmetic is the same whatever the key, and a rejected result \
        is cleared under the mask. Each prime's working space at the width of `n` reduces the \
        input modulo the prime by two Montgomery products; a narrow working space then takes the \
        prime, its own Montgomery constants and the reduced input at the prime's width \
        (`max(2, ⌈len/8⌉)` limbs of 64 bits for its public length), where the exponentiation \
        follows a fixed schedule over 32-bit limbs, its squarings by a dedicated Montgomery \
        square. `qInv` is reduced as a signed coefficient \
        and the result recombined in a double-width product, at the width of `n`."]
    code := Impl.Bignum.Arm.CrtFn.code
    stack := 56
    verified := Proof.Bignum.Arm.crt_verified },
  Spec.Rsa.privateCrtApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["The shared UMAAL integrated Montgomery scan supplies the private exponentiation's \
        products and squares through the same window and CRT proofs, fully unrolled for primes \
        of 16 and 32 limbs of 32 bits (the public width selects the scan). Other arithmetic rows \
        use the shared exact UMAAL row transformation."]
    code := Impl.Bignum.Arm.CrtFios.code
    stack := 56
    verified := Proof.Bignum.Arm.crtUmaal_verified
    features := ["umaal"] },
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
    verified := Proof.Rsa.Arm.CrtValues.crt_values_verified },
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7, frameless (the callee-saved registers are kept in the working \
        space): `n` and `e` are checked first, the only branches on data. The numbers are read \
        into 32-bit limbs at the width of `n`, and every check computed and and'ed into a mask: \
        `p q = n` as `p` odd with `n / p = q` and `n mod p = 0`, by a fixed-iteration long \
        division; `d < n`, `dP < p - 1`, `dQ < q - 1` and `qInv < p` by a subtraction's borrow; \
        `e dP ≡ 1`, `e dQ ≡ 1` and `q qInv ≡ 1` by binary multiplication modulo `p - 1`, `q - 1` \
        or `p` (over the 33 bits of `e`, or the bits of `q`), its additions selected under masks; \
        and `d e ≡ 1` modulo `p - 1` and `q - 1` as `d mod (p - 1) = dP` and \
        `d mod (q - 1) = dQ`, by the same division, `dP` and `dQ` being the inverses of `e` once \
        their own checks hold."]
    code := Impl.Rsa.Arm.CheckKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckKey.check_key_verified },
  Spec.Rsa.checkCrtKeyApi.artifact Arm.target {
    notes := ["Baseline ARMv7, frameless (the callee-saved registers are kept in the working \
        space): `n` and `e` are checked first, the only branches on data. The numbers are read \
        into 32-bit limbs at the width of `n`, and every check computed and and'ed into a mask: \
        `p q = n` as `p` odd with `n / p = q` and `n mod p = 0`, by a fixed-iteration long \
        division; `dP < p - 1`, `dQ < q - 1` and `qInv < p` by a subtraction's borrow; and \
        `e dP ≡ 1`, `e dQ ≡ 1` and `q qInv ≡ 1` by binary multiplication modulo `p - 1`, \
        `q - 1` or `p` (over the 33 bits of `e`, or the bits of `q`), its additions selected \
        under masks."]
    code := Impl.Rsa.Arm.CheckCrtKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckCrtKey.check_crt_key_verified },
  Spec.Rsa.recoverPrimesApi.artifact Arm.target {
    notes := ["Baseline ARMv7: check `n`, form `d e - 1`, and prepare Montgomery arithmetic. \
        Each public candidate (2 through 101) uses one fixed-width, most-significant-bit \
        pass over the exponent, fusing exponentiation with root detection. Each bit uses \
        the specialized Montgomery square; multiplication by 2 or 3 uses shared modular \
        additions, and later candidates use Montgomery multiplication. Set bits reset the \
        root chain under masks. Only the number of candidates tried may leak. Shared \
        fixed-iteration GCD and division recover the factors and write the larger first, \
        or zero both outputs when recovery fails."]
    code := Impl.Rsa.Arm.RecoverFused.code
    stack := 56
    verified := Proof.Rsa.Arm.Recover.recover_primes_fused_verified },
  Spec.Rsa.recoverPrimesApi.artifact Arm.target {
    suffix := "_umaal"
    notes := ["The baseline prime recovery with the shared UMAAL row transformation used \
        by private RSA, retaining the same arithmetic, checks and timing contract."]
    code := Impl.Bignum.Arm.umaalArithmetic Impl.Rsa.Arm.RecoverFused.code
    stack := 56
    verified := Proof.Rsa.Arm.Recover.recover_primes_fused_umaal_verified
    features := ["umaal"] }]

end VG.Artifacts.Rsa.Arm
