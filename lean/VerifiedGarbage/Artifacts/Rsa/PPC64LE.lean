module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Rsa.Contract
public import VerifiedGarbage.Spec.Rsa.PrivatePrecompute
public import VerifiedGarbage.Spec.Rsa.RecoverDet
import VerifiedGarbage.Proof.Rsa.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA (RFC 8017) on PPC64LE -/

namespace VG.Artifacts.Rsa.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Rsa.publicPrecomputeApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.publicPrecompute
    verified := Proof.Rsa.PPC64LE.Scrub.publicPrecompute_scrubbed },
  Spec.Rsa.privatePrecomputeApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.privatePrecompute
    verified := Proof.Rsa.PPC64LE.Scrub.privatePrecompute_scrubbed },
  Spec.Rsa.crtValuesApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.crtValues
    verified := Proof.Rsa.PPC64LE.Scrub.crtValues_scrubbed },
  Spec.Rsa.checkKeyApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.checkKey
    verified := Proof.Rsa.PPC64LE.Scrub.checkKey_scrubbed },
  Spec.Rsa.recoverPrimesDetApi.artifact PPC64LE.target {
    code := Impl.Rsa.PPC64LE.Fn.recoverPrimesDet
    verified := Proof.Rsa.PPC64LE.Scrub.recoverPrimesDet_scrubbed }]

spec_apis artifacts

end VG.Artifacts.Rsa.PPC64LE
