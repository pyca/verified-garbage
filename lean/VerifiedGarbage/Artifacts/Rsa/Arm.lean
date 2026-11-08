module

public import VerifiedGarbage.Proof.Bignum.Arm.PcVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtVerified
public import VerifiedGarbage.Proof.Bignum.Arm.CrtUmaal
public import VerifiedGarbage.Proof.Bignum.Arm.PdVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CvVerified
public import VerifiedGarbage.Proof.Rsa.Arm.CkVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.Arm.InvLoop
public import VerifiedGarbage.Proof.Rsa.Arm.RdTop
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Rsa.Arm.PrivImpl
public import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm

/-! # RSA (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rsa.Arm

def direct : List Artifact := [
  Spec.Rsa.crtValuesApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CrtValues.code
    stack := 0
    verified := Proof.Rsa.Arm.CrtValues.crt_values_verified },
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CheckKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckKey.check_key_verified },
  Spec.Rsa.recoverPrimesDetApi.artifact Arm.target {
    code := Impl.Rsa.Arm.RecoverDet.code
    stack := 56
    verified := Proof.Rsa.Arm.Recover.recover_primes_det_verified }]

end VG.Artifacts.Rsa.Arm

-- The RSA modulus' precomputed values on ARMv7, for each private CRT implementation
namespace VG.Artifacts.Rsa.Arm.RsaPrivateCrt

open VG.Proof.Rsa.Arm

def artifacts (v : CrtImpl) : List Artifact := [
  Spec.Rsa.publicPrecomputeApi.artifact Arm.target {
    suffix := v.suffix
    code := v.pc
    stack := 56
    verified := v.pcVerified
    features := v.features }]

end VG.Artifacts.Rsa.Arm.RsaPrivateCrt

namespace VG.Artifacts.Rsa.Arm

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun v => RsaPrivateCrt.artifacts v)

end VG.Artifacts.Rsa.Arm
