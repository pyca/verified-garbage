module

public import VerifiedGarbage.Proof.RsaPkcs1Enc.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSAES-PKCS1-v1_5 (RFC 8017) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaPkcs1Enc.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaPkcs1Enc.decryptPrecomputedApi.artifact PPC64LE.target
    Proof.RsaPkcs1Enc.PPC64LE.Scrub.decryptPrecomputedReg,
  Spec.RsaPkcs1Enc.encryptRandomApi.artifact PPC64LE.target Proof.RsaPkcs1Enc.PPC64LE.Scrub.encryptRandomReg]

end VG.Artifacts.RsaPkcs1Enc.PPC64LE
