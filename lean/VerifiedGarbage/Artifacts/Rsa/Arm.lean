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
public import VerifiedGarbage.Proof.Variants.RsaInverse.Arm
public import VerifiedGarbage.Proof.Bignum.Arm.PrivPreVerified

/-! # RSA (RFC 8017) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.Rsa.Arm

def direct : List Artifact := [
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Rsa.Arm.CheckKey.codeU
    stack := 0
    verified := Proof.Rsa.Arm.CheckKey.check_key_umaal_verified },
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    code := Impl.Rsa.Arm.CheckKey.code
    stack := 0
    verified := Proof.Rsa.Arm.CheckKey.check_key_verified },
  Spec.Rsa.privatePrecomputeApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Bignum.Arm.PrivPreFn.codeU
    stack := 168
    verified := Proof.Bignum.Arm.privPre_umaal_verified },
  Spec.Rsa.privatePrecomputeApi.artifact Arm.target {
    code := Impl.Bignum.Arm.PrivPreFn.code
    stack := 168
    verified := Proof.Bignum.Arm.privPre_verified }]

end VG.Artifacts.Rsa.Arm

namespace VG.Artifacts.Rsa.Arm

open VG.Proof.Rsa.Arm

def artifacts : List Artifact :=
  (VG.Proof.Variants.RsaInverse.Arm.variants.flatMap fun v => [
    Spec.Rsa.crtValuesApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Rsa.Arm.CrtValues.codeFor v.um
      stack := 0
      verified := Proof.Rsa.Arm.CrtValues.crt_values_for_verified v.um },
    Spec.Rsa.recoverPrimesDetApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Rsa.Arm.RecoverDet.codeFor v.um
      stack := 56
      verified := Proof.Rsa.Arm.Recover.recover_primes_det_for_verified v.um }]) ++
  direct ++
  (VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) => [
    Spec.Rsa.publicPrecomputeApi.artifact Arm.target {
      suffix := v.suffix
      code := v.pc
      stack := 56
      verified := v.pcVerified }])

end VG.Artifacts.Rsa.Arm
