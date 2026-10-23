module

public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPublic.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckDomain.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Exchange.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.CheckPrivate.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Derive.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.GenerateKey.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.AArch64.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Ffdh.AArch64.Generation.Init
import Mathlib.Tactic.Finiteness.Attr
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Artifacts.Ffdh.AArch64
open VG.AArch64

def artifacts : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p (its 32-entry window table \
        included). y is compared with 1 and with p − 1 by a subtraction's borrow over all the words; \
        with q, `R² mod p` is computed by doublings and squarings and `y^q mod p` by RSA's \
        exponentiation with five-bit windows (the `vg_rsa_square_window5` helper and a constant-time \
        table scan) from q's first nonzero octet."]
    code := Impl.Ffdh.AArch64.Domain.CheckPublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPublic.cp_verified _ _ _ },
  Spec.Ffdh.checkDomainApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p. g and q are compared with \
        1 and with p − 1 by a subtraction's borrow over all the words; `q ∣ p − 1` is a Montgomery \
        reduction of p − 1 modulo q, in a workspace for q's significant octets, compared with zero; \
        `g^q mod p` is computed by RSA's exponentiation with five-bit windows (the \
        `vg_rsa_square_window5` helper and a constant-time table scan) from q's first nonzero octet."]
    code := Impl.Ffdh.AArch64.Domain.CheckDomain.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckDomain.cd_verified _ _ _ },
  Spec.Ffdh.exchangeApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p. `y^x mod p` is computed by \
        RSA's exponentiation with five-bit windows over all `x_len` octets of x (the \
        `vg_rsa_square_window5` helper and a constant-time table scan); z is compared with 1 and \
        with p − 1 by a subtraction's borrow over all the words, and stored masked by the result, \
        zeros for 0, without a branch."]
    code := Impl.Ffdh.AArch64.Domain.Exchange.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Exchange.ex_verified _ _ _ },
  Spec.Ffdh.checkPrivateApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p. x's range and y's are \
        comparisons by a subtraction's borrow over all the words, and the only branch on x is on \
        its range; with q, `y^q mod p` and then `g^x mod p` are computed by RSA's exponentiation \
        with five-bit windows (the `vg_rsa_square_window5` helper and a constant-time table scan), \
        the latter over all `x_len` octets of x, and compared with y over all the words."]
    code := Impl.Ffdh.AArch64.Domain.CheckPrivate.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.CheckPrivate.kp_verified _ _ _ },
  Spec.Ffdh.derivePublicApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p. x's range is a comparison \
        by a subtraction's borrow over all the words, as in `vg_ffdh_check_private`, and the only \
        branch on x is on its range; `g^x mod p` is computed by RSA's exponentiation with five-bit \
        windows (the `vg_rsa_square_window5` helper and a constant-time table scan) over all `x_len` \
        octets of x, compared with 1 and with p − 1 by a subtraction's borrow over all the words, and \
        stored masked by the result, zeros for 3, without a branch. Powers of a checked generator \
        remain in its q subgroup, so y needs only its range check."]
    code := Impl.Ffdh.AArch64.Domain.DerivePublic.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.Derive.dv_verified _ _ _ },
  Spec.Ffdh.generateKeyApi.artifact target {
    notes := ["Baseline AArch64: p is checked as `vg_rsa_public_precompute` checks a modulus, in a \
        working space of `w = ⌈p_len / 8⌉` words with an inner one for p. The scalar's octets are cut \
        from `rand` by a loop over all `p_len` of them, written to `x`, and its range is a \
        comparison by a subtraction's borrow over all the words; the only branch on it is on its \
        range. `g^x mod p` is computed by RSA's exponentiation with five-bit windows (the \
        `vg_rsa_square_window5` helper and a constant-time table scan) over x's octets from the \
        bound's first nonzero one, and stored to `y`; with q, `y^q mod p` too. x and y are then \
        masked by y's validity, zeros for 3, without a branch."]
    code := Impl.Ffdh.AArch64.Domain.GenerateKey.code Proof.Bignum.AArch64.WindowFive.called.code
      Proof.Bignum.AArch64.WindowVector.selector.code Proof.Bignum.AArch64.Mont.base.mm
    verified := Proof.Ffdh.AArch64.GenerateKey.gk_verified _ _ _ },
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.AArch64.Generation.init
    verified := Proof.Ffdh.AArch64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.AArch64.KeyGeneration.init
    verified := Proof.Ffdh.AArch64.KeyGeneration.init_verified },
  Spec.Ffdh.keySearchApi.artifact target {
    stack := 48
    notes := ["The whole key search runs in verified code: both rejection budgets, the \
        octets each attempt consumes, and the next entropy request. Each attempt calls \
        `vg_ffdh_generate_key`, in a frame of 32 bytes holding its stack arguments, within \
        a frame saving `x30`. Timing depends on the domain, the controller's public words and \
        the attempts' statuses."]
    code := Proof.Ffdh.AArch64.KeyGeneration.keyCode
    verified := Proof.Ffdh.AArch64.KeyGeneration.key_verified_base }]

end VG.Artifacts.Ffdh.AArch64
