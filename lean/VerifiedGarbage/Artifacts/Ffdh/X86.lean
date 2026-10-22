module

public import VerifiedGarbage.Proof.Ffdh.X86.CheckDomainVerified
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPublicVerified
public import VerifiedGarbage.Proof.Ffdh.X86.CheckPrivateVerified
public import VerifiedGarbage.Proof.Ffdh.X86.ExchangeVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeyInit
public import VerifiedGarbage.Proof.Ffdh.X86.KeyGenVerified
public import VerifiedGarbage.Proof.Ffdh.X86.KeySearch.Verified
public import VerifiedGarbage.Proof.Ffdh.X86.Shape
public import VerifiedGarbage.Proof.Framework.Registration

/-! FFDH's domain and key checks, exchange and key generation on baseline i686. -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
  Spec.Ffdh.checkDomainApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at a run-time width, at p's width, reading \
      their arguments from a frame of synthetic arguments; every Montgomery multiplication calls \
      `vg_rsa_mont_mul_at`. The subgroup check is a fixed four-bit-window power. The domain's \
      bytes choose the branches. Callee-saved registers reside in scratch."]
    code := Impl.Ffdh.X86.CheckDomain.code
    verified := Proof.Ffdh.X86.CheckDomain.verified
    spSafe := Proof.Ffdh.X86.Shape.checkDomain_spSafe
    stack := 116 },
  Spec.Ffdh.checkPublicApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at p's width, as `vg_ffdh_check_domain` does. \
      The subgroup check is a fixed four-bit-window power. The domain's and y's bytes choose the \
      branches. Callee-saved registers reside in scratch."]
    code := Impl.Ffdh.X86.CheckPublic.code
    verified := Proof.Ffdh.X86.CheckPublic.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPublic_spSafe
    stack := 116 },
  Spec.Ffdh.checkPrivateApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at p's width, as `vg_ffdh_check_domain` does. \
      The scalar's range is the one branch on x; the power of g is a fixed four-bit-window power \
      over all of p's width, and its comparison with y is masked. Powers of a checked generator \
      remain in its q subgroup, so the generated power needs only its range check. Callee-saved \
      registers reside in scratch."]
    code := Impl.Ffdh.X86.CheckPrivate.code
    verified := Proof.Ffdh.X86.CheckPrivate.verified
    spSafe := Proof.Ffdh.X86.Shape.checkPrivate_spSafe
    stack := 116 },
  Spec.Ffdh.exchangeApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at p's width, as `vg_ffdh_check_domain` does. \
      The power is a fixed four-bit-window power over all of p's width, scanning the whole table \
      for each window; z's range is the acceptance mask, which clears the output, and the code has \
      no branch. Callee-saved registers reside in scratch."]
    code := Impl.Ffdh.X86.Exchange.code
    verified := Proof.Ffdh.X86.Exchange.verified
    spSafe := Proof.Ffdh.X86.Shape.exchange_spSafe
    stack := 116 },
  Spec.Ffdh.keyInitApi.artifact X86.target {
    code := Impl.Ffdh.X86.KeyInit.code
    verified := Proof.Ffdh.X86.KeyInit.verified },
  Spec.Ffdh.generateKeyApi.artifact X86.target {
    notes := ["Runs on private CRT RSA's operations at p's width, as `vg_ffdh_check_domain` does. \
      The bound's octets are scanned and `rand`'s cut to its bit length without a branch; the \
      scalar's range is the one branch on x. The power of g is a fixed four-bit-window power over \
      all of p's width; y's range and, with q, its subgroup membership are the acceptance mask, \
      which clears both outputs. Callee-saved registers reside in scratch."]
    code := Impl.Ffdh.X86.GenerateKey.code
    verified := Proof.Ffdh.X86.KeyGen.verified
    spSafe := Proof.Ffdh.X86.Shape.generateKey_spSafe
    stack := 116 },
  Spec.Ffdh.keySearchApi.artifact X86.target {
    notes := ["The whole key search runs in verified code: both rejection budgets, the octets each attempt \
      consumes, and the next entropy request. Each attempt calls `vg_ffdh_generate_key` with its eleven \
      arguments in a 44-byte frame. The controller's words live in the state; timing depends on the domain, \
      the controller's public words and the attempts' statuses."]
    code := Impl.Ffdh.X86.KeySearch.code
    verified := Proof.Ffdh.X86.KeySearch.verified
    spSafe := Proof.Ffdh.X86.Shape.keySearch_spSafe
    stack := 164 }]

end VG.Artifacts.Ffdh.X86
