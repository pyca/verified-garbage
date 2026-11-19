module

public import VerifiedGarbage.Proof.Sha3.PPC64LE.Instances
public import VerifiedGarbage.Proof.Sha3.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # SHA-3 and SHAKE (FIPS 202) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Sha3.PPC64LE

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeSha3_224Reg,
  Spec.Sha3.updateSha3_256Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeSha3_256Reg,
  Spec.Sha3.updateSha3_384Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeSha3_384Reg,
  Spec.Sha3.updateSha3_512Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeSha3_512Reg,
  Spec.Sha3.updateShake128Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact PPC64LE.target Proof.Sha3.PPC64LE.Scrub.squeezeShake256Reg]

end VG.Artifacts.Sha3.PPC64LE
