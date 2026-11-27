module

public import VerifiedGarbage.TCB.Arm.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Rsa.Arm.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.RsaPrivateCrt.Arm
import VerifiedGarbage.Proof.Variants.RsaMont.Arm
import VerifiedGarbage.Proof.Variants.RsaInverse.Arm
import VerifiedGarbage.Proof.Rsa.Arm.InvLoop
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA (RFC 8017) on ARMv7 -/

namespace VG.Artifacts.Rsa.Arm

def direct : List (Artifact Arm.target) := [
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    suffix := "_umaal"
    code := Impl.Rsa.Arm.Fn.checkKeyU
    verified := Proof.Rsa.Arm.Fn.checkKeyU },
  Spec.Rsa.checkKeyApi.artifact Arm.target {
    code := Impl.Rsa.Arm.Fn.checkKey
    verified := Proof.Rsa.Arm.Fn.checkKey }]

end VG.Artifacts.Rsa.Arm

namespace VG.Artifacts.Rsa.Arm

open VG.Proof.Rsa.Arm

public def artifacts : List (Artifact Arm.target) :=
  (VG.Proof.Variants.RsaInverse.Arm.variants.flatMap fun (v : Proof.Variants.RsaInverse.Arm.Variant) => [
    Spec.Rsa.crtValuesApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Rsa.Arm.Fn.crtValues v.um
      verified := Proof.Rsa.Arm.Fn.crtValues v.um },
    Spec.Rsa.recoverPrimesDetApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Rsa.Arm.Fn.recoverPrimesDet v.um
      verified := Proof.Rsa.Arm.Fn.recoverPrimesDet v.um }]) ++
  direct ++
  (VG.Proof.Variants.RsaMont.Arm.variants.map fun (b : Proof.Bignum.Arm.MontBackend) =>
    Spec.Rsa.privatePrecomputeApi.artifact Arm.target {
      suffix := b.suffix
      code := Impl.Rsa.Arm.Fn.privatePrecompute (Proof.Rsa.Arm.privatePrecomputeCode b)
      verified := Proof.Rsa.Arm.Fn.privatePrecompute b }) ++
  (VG.Proof.Variants.RsaPrivateCrt.Arm.variants.flatMap fun (v : CrtImpl) => [
    Spec.Rsa.publicPrecomputeApi.artifact Arm.target {
      suffix := v.suffix
      code := Impl.Rsa.Arm.Fn.publicPrecompute v.pc
      verified := Proof.Rsa.Arm.Fn.publicPrecompute v }])

spec_apis artifacts

end VG.Artifacts.Rsa.Arm
