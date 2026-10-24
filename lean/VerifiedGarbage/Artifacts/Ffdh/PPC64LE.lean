module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.CheckDomainVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Domain.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Finite-field Diffie–Hellman on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def artifacts : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    notes := ["The model has no carry bit, so `bits` is first checked to be below `2^14` (a branch \
        on a public value), and the bounds are then sign bits of 64-bit differences."]
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := Proof.Ffdh.PPC64LE.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    notes := ["The model has no carry bit, so `p_len` is first checked to be below `2^11` (a branch \
        on a public value), and the bounds are then sign bits of 64-bit differences."]
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := Proof.Ffdh.PPC64LE.KeyGeneration.init_verified },
  Spec.Ffdh.checkPublicApi.artifact PPC64LE.target {
    notes := ["p is loaded and checked as `vg_rsa_public_precompute` checks a modulus, in RSA's public \
        working space of `w = ⌈p_len / 8⌉` words; y is compared with p by a subtraction's borrow and \
        with 0, 1 and p − 1 by equality masks over all the words; with q, `y^q mod p` is computed by \
        RSA's bit-serial exponentiation (`R² mod p` by doublings) and compared with 1. The \
        nonvolatile registers are saved in the working space's header."]
    code := Impl.Ffdh.PPC64LE.Domain.checkPublic
    verified := Proof.Ffdh.PPC64LE.Domain.cp_verified },
  Spec.Ffdh.checkDomainApi.artifact PPC64LE.target {
    notes := ["p is loaded and checked as `vg_rsa_public_precompute` checks a modulus, in RSA's public \
        working space of `w = ⌈p_len / 8⌉` words; g and q are compared with p by a subtraction's borrow \
        and with 0, 1 and p − 1 by equality masks over all the words, and q's oddness is its last \
        octet's; `q ∣ p − 1` is `p mod q = 1`, p's octets reduced modulo q by doublings; `g^q mod p` is \
        computed by RSA's bit-serial exponentiation (`R² mod p` by doublings) and compared with 1. The \
        nonvolatile registers are saved in the working space's header."]
    code := Impl.Ffdh.PPC64LE.Domain.checkDomain
    verified := Proof.Ffdh.PPC64LE.Domain.cd_verified },
  Spec.Ffdh.exchangeApi.artifact PPC64LE.target {
    notes := ["p is loaded and checked as `vg_rsa_public_precompute` checks a modulus, in RSA's public \
        working space of `w = ⌈p_len / 8⌉` words, whose address is the second argument on the stack; \
        `z = y^x mod p` is computed by a Montgomery square and a multiplication selected by a mask for \
        every bit of all `x_len` octets of x (`R² mod p` by doublings), compared with 0, 1 and p − 1 by equality masks over all the words, and \
        written to `out` or replaced by zeros under the mask. The nonvolatile registers, and x's and \
        `out`'s addresses and x's length, are saved in the working space's header."]
    code := Impl.Ffdh.PPC64LE.Domain.exchange
    verified := Proof.Ffdh.PPC64LE.Domain.ex_verified },
  Spec.Ffdh.derivePublicApi.artifact PPC64LE.target {
    notes := ["p is loaded and checked as `vg_rsa_public_precompute` checks a modulus, in RSA's public \
        working space of `w = ⌈p_len / 8⌉` words; x's range is a comparison with q (`p − 1` without q) \
        by a subtraction's borrow and with 0 by an equality mask over all the words, and the only branch \
        on x is on its range. `g^x mod p` is computed as `vg_ffdh_exchange` computes the shared value, by \
        a Montgomery square and a multiplication selected by a mask for every bit of all `x_len` octets \
        of x, compared with 0, 1 and p − 1 by equality masks over all the words, and written to `y` or \
        replaced by zeros under the mask. Powers of a checked generator remain in its q subgroup, so y \
        needs only its range check. The nonvolatile registers, and x's and `y`'s addresses and x's \
        length, are saved in the working space's header."]
    code := Impl.Ffdh.PPC64LE.Derive.derivePublic
    verified := Proof.Ffdh.PPC64LE.Derive.dp_verified },
  Spec.Ffdh.checkPrivateApi.artifact PPC64LE.target {
    notes := ["p is loaded and checked as `vg_rsa_public_precompute` checks a modulus, in RSA's public \
        working space of `w = ⌈p_len / 8⌉` words; x's range is checked as `vg_ffdh_derive_public` checks \
        it, and the only branch on x is on its range. `g^x mod p` is computed as `vg_ffdh_exchange` \
        computes the shared value, over all `x_len` octets of x, and compared with 0, 1, p − 1 and y by \
        equality masks over all the words: for x in range, y is valid and `y = g^x mod p` exactly when \
        `g^x mod p` is in `2..p − 2` and equals y, since powers of a checked generator remain in its q \
        subgroup. The nonvolatile registers, and x's and y's addresses and x's length, are saved in the \
        working space's header."]
    code := Impl.Ffdh.PPC64LE.CheckPrivate.checkPrivate
    verified := Proof.Ffdh.PPC64LE.CheckPrivate.kp_verified }]

end VG.Artifacts.Ffdh.PPC64LE
