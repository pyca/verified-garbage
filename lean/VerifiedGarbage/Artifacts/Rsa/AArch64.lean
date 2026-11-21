module

public import VerifiedGarbage.Proof.Rsa.AArch64.InvBatch
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.AArch64.Fn
public import VerifiedGarbage.TCB.AArch64.Print

/-! # RSA (RFC 8017) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Rsa.AArch64

def artifacts : List Artifact := [
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

end VG.Artifacts.Rsa.AArch64
