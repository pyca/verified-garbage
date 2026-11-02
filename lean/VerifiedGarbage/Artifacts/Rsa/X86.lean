module
public import VerifiedGarbage.Proof.Rsa.X86.BatchInstance

public import VerifiedGarbage.Proof.Bignum.X86.CrtRt.TimeTop
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputedRt.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PublicRt.Verified
public import VerifiedGarbage.Proof.Bignum.X86.PrecomputeVerified
public import VerifiedGarbage.Proof.Rsa.X86.CvVerified
public import VerifiedGarbage.Proof.Rsa.X86.KcVerified
public import VerifiedGarbage.Proof.Rsa.X86.RvVerified
public import VerifiedGarbage.Proof.Rsa.X86.Rd.Timing
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.X86.RtShape

/-! # Public and private CRT RSA on baseline i686 -/

@[expose] public section
namespace VG.Artifacts.Rsa.X86

def artifacts : List Artifact := [
  Spec.Rsa.recoverPrimesApi.artifact X86.target {
    code := Impl.Rsa.X86.RecoverRt.code
    verified := Proof.Rsa.X86.Recover.verified
    spSafe := Proof.Rsa.X86.RtShape.recover_spSafe
    stack := 96 },
  Spec.Rsa.recoverPrimesDetApi.artifact X86.target {
    code := Impl.Rsa.X86.RecoverDetRt.code
    verified := Proof.Rsa.X86.Recover.verifiedD
    spSafe := Proof.Rsa.X86.RtShape.recoverDet_spSafe
    stack := 96 },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.KeyCheckRt.code true
    verified := Proof.Rsa.X86.KeyCheck.verified true
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe true
    stack := 20 },
  Spec.Rsa.checkCrtKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.KeyCheckRt.code false
    verified := Proof.Rsa.X86.KeyCheck.verified false
    spSafe := Proof.Rsa.X86.RtShape.check_spSafe false
    stack := 20 },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    code := Impl.Rsa.X86.CrtValuesRt.code
    verified := Proof.Rsa.X86.CrtValues.verified
    spSafe := Proof.Rsa.X86.RtShape.crtValues_spSafe
    stack := 52 },
  Spec.Rsa.publicPrecomputedCheckedApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputedRt.code
    verified := Proof.Bignum.X86.PrecomputedRt.verified
    spSafe := Proof.Rsa.X86.RtShape.precomputed_spSafe
    stack := 96 },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Bignum.X86.PrecomputeFn.code
    verified := Proof.Bignum.X86.precompute_verified
    stack := 96 }]

end VG.Artifacts.Rsa.X86
