module

public import VerifiedGarbage.Proof.RsaPkcs1Sig.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSASSA-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Sig.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Sig.verifyPrecomputedApi.artifact PPC64LE.target
    Proof.RsaPkcs1Sig.PPC64LE.Scrub.verifyPrecomputedReg,
  Spec.RsaPkcs1Sig.recoverPrecomputedApi.artifact PPC64LE.target
    Proof.RsaPkcs1Sig.PPC64LE.Scrub.recoverPrecomputedReg,
  Spec.RsaPkcs1Sig.signPrecomputedApi.artifact PPC64LE.target Proof.RsaPkcs1Sig.PPC64LE.Scrub.signPrecomputedReg]

end VG.Artifacts.RsaPkcs1Sig.PPC64LE
