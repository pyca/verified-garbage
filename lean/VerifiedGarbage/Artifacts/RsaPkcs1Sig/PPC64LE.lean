module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.verifyPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.verifyPrecomputed_scrubbed },
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.recoverPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.recoverPrecomputed_scrubbed },
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact PPC64LE.target {
    code := Impl.RsaPkcs1Sig.PPC64LE.Fn.signPrecomputed
    verified := Proof.RsaPkcs1Sig.PPC64LE.Scrub.signPrecomputed_scrubbed }]

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
