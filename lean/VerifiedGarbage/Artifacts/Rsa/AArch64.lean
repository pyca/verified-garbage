module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.AArch64.InvBatch
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Rsa.AArch64.Fn
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA (RFC 8017) on AArch64 -/

namespace VG.Artifacts.Rsa.AArch64

public def artifacts : List (Artifact AArch64.target) := [
  Spec.Rsa.publicPrecomputeApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Fn.publicPrecompute
    verified := Proof.Rsa.AArch64.Fn.publicPrecompute },
  Spec.Rsa.privatePrecomputeApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Fn.privatePrecompute
    verified := Proof.Rsa.AArch64.Fn.privatePrecompute },
  Spec.Rsa.crtValuesApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Fn.crtValues
    verified := Proof.Rsa.AArch64.Fn.crtValues },
  Spec.Rsa.recoverPrimesDetApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Fn.recoverPrimesDet
    verified := Proof.Rsa.AArch64.Fn.recoverPrimesDet },
  Spec.Rsa.checkKeyApi.artifact AArch64.target {
    code := Impl.Rsa.AArch64.Fn.checkKey
    verified := Proof.Rsa.AArch64.Fn.checkKey }]

spec_apis artifacts

end VG.Artifacts.Rsa.AArch64
