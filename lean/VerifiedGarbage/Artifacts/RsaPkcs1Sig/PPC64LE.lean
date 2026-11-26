module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Precomputed
public import VerifiedGarbage.Spec.RsaPkcs1Sig.Contract
import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

namespace VG.Artifacts.RsaPkcs1Sig.PPC64LE

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.verifyPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.verifyPrecomputed_scrubbed },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.recoverPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.recoverPrecomputed_scrubbed },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.signPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.signPrecomputed_scrubbed }]

spec_apis artifacts

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
