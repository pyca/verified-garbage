module

public import VerifiedGarbage.Proof.Bignum.PPC64LE.PreVerified
public import VerifiedGarbage.Proof.Bignum.PPC64LE.CrtVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.CvVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Instances
public import VerifiedGarbage.Proof.Rsa.PPC64LE.KcVerified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.RdVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSA (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Rsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Bignum.PPC64LE.Precompute.precompute
    verified := Proof.Bignum.PPC64LE.Pre.precompute_verified },
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.CrtValues.code
    verified := Proof.Rsa.PPC64LE.CrtValues.cv_verified },
  Spec.Rsa.checkKeyApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.CheckKey.code
    verified := Proof.Rsa.PPC64LE.KeyCheck.ck_verified },
  Spec.Rsa.recoverPrimesDetApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.RecoverDet.code
    verified := Proof.Rsa.PPC64LE.RecDet.rd_verified }]

end VG.Artifacts.Rsa.PPC64LE
