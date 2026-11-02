module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.PublicVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CvVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CckVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CkVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.Arm.InvLoop
public import VerifiedGarbage.Proof.Rsa.Arm.RdTop

/-! # RSA (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rsa.Arm

def artifacts : List Artifact := [
  Spec.Rsa.crtValuesApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CrtValues.code
    stack := 0
    verified := Proof.Rsa.Arm.CrtValues.crt_values_verified },
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CheckKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckKey.check_key_verified },
  Spec.Rsa.checkCrtKeyApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CheckCrtKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckCrtKey.check_crt_key_verified },
  Spec.Rsa.recoverPrimesDetApi.artifact Arm.target {
    code := Impl.Rsa.Arm.RecoverDet.code
    stack := 56
    verified := Proof.Rsa.Arm.Recover.recover_primes_det_verified }]

end VG.Artifacts.Rsa.Arm
