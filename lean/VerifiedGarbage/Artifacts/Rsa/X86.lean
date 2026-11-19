module
public import VerifiedGarbage.Proof.Rsa.X86.BatchInstance

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Bignum.X86.PrivPre.Instance
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.Rd.TimingW
public import VerifiedGarbage.Proof.Rsa.X86.Rd.GcdDone
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.X86.RtShape
public import VerifiedGarbage.TCB.X86.Print

/-! # RSA (RFC 8017) on x86 -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesDetApi.artifact X86.target {
    code := Impl.Rsa.X86.RecoverDetRt.code
    verified := .unscrubbed Proof.Rsa.X86.Recover.verifiedD
    spSafe := Proof.Rsa.X86.RtShape.recoverDet_spSafe },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.KeyCheckRt.code true
    verified := .unscrubbed (Proof.Rsa.X86.KeyCheck.verified true)
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe true },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    code := Impl.Rsa.X86.CrtValuesRt.code
    verified := .unscrubbed Proof.Rsa.X86.CrtValues.verified
    spSafe := Proof.Rsa.X86.RtShape.crtValues_spSafe },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputeFn.code
    verified := .unscrubbed Proof.Bignum.X86.precompute_verified },
  Spec.Rsa.privatePrecomputeApi.artifact X86.target {
    code := Proof.Bignum.X86.PrivPre.ppCode
    verified := .unscrubbed Proof.Bignum.X86.PrivPre.pp_verified
    spSafe := Proof.Bignum.X86.PrivPre.pp_spSafe }]

end VG.Artifacts.Rsa.X86
