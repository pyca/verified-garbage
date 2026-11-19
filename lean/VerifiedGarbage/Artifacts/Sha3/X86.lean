module

public import VerifiedGarbage.Proof.Sha3.X86.Absorb
public import VerifiedGarbage.Proof.Sha3.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha3.X86.Lit

/-! # SHA-3 and SHAKE (FIPS 202) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86

def artifacts : List Artifact := [
  Spec.Sha3.updateSha3_224Api.artifact X86.target Proof.Sha3.X86.Absorb.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeSha3_224Reg,
  Spec.Sha3.updateSha3_256Api.artifact X86.target Proof.Sha3.X86.Absorb.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeSha3_256Reg,
  Spec.Sha3.updateSha3_384Api.artifact X86.target Proof.Sha3.X86.Absorb.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeSha3_384Reg,
  Spec.Sha3.updateSha3_512Api.artifact X86.target Proof.Sha3.X86.Absorb.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeSha3_512Reg,
  Spec.Sha3.updateShake128Api.artifact X86.target Proof.Sha3.X86.Absorb.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact X86.target Proof.Sha3.X86.Scrub.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact X86.target Proof.Sha3.X86.Scrub.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact X86.target Proof.Sha3.X86.Scrub.squeezeShake256Reg]

end VG.Artifacts.Sha3.X86
