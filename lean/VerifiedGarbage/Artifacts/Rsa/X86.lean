module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rsa.RecoverDet
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
import VerifiedGarbage.Proof.Rsa.X86.Scrub
import VerifiedGarbage.Impl.Rsa.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA (RFC 8017) on x86 -/

namespace VG.Artifacts.Rsa.X86

public def artifacts : List (Artifact X86.target) := [
  Spec.Rsa.recoverPrimesDetApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.recoverPrimesDet
    verified := Proof.Rsa.X86.Scrub.recoverPrimesDet_scrubbed },
  Spec.Rsa.checkKeyApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.checkKey
    verified := Proof.Rsa.X86.Scrub.checkKey_scrubbed },
  Spec.Rsa.crtValuesApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.crtValues
    verified := Proof.Rsa.X86.Scrub.crtValues_scrubbed },
  Spec.Rsa.publicPrecomputeApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.publicPrecompute
    verified := Proof.Rsa.X86.Scrub.publicPrecompute_scrubbed },
  Spec.Rsa.privatePrecomputeApi.artifact X86.target {
    code := Impl.Rsa.X86.Fn.privatePrecompute
    verified := Proof.Rsa.X86.Scrub.privatePrecompute_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rsa.X86
