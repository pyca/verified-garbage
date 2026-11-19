module
import VerifiedGarbage.Proof.MlDsa.X86_64.CalleeLit

public import VerifiedGarbage.Proof.Sha3.X86_64.Instances
public import VerifiedGarbage.Proof.Sha3.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # SHA-3 and SHAKE (FIPS 202) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sha3.X86_64

def artifacts : List Artifact := [
  Spec.Sha3.absorbSha3_224Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.absorbSha3_224Reg,
  Spec.Sha3.finalizeSha3_224Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeSha3_224Reg,
  Spec.Sha3.absorbSha3_256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.absorbSha3_256Reg,
  Spec.Sha3.finalizeSha3_256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeSha3_256Reg,
  Spec.Sha3.absorbSha3_384Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.absorbSha3_384Reg,
  Spec.Sha3.finalizeSha3_384Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeSha3_384Reg,
  Spec.Sha3.absorbSha3_512Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.absorbSha3_512Reg,
  Spec.Sha3.finalizeSha3_512Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeSha3_512Reg,
  Spec.Sha3.absorbShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.absorbShake128Reg,
  Spec.Sha3.finalizeShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeShake128Reg,
  Spec.Sha3.squeezeShake128Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.squeezeShake128Reg,
  Spec.Sha3.finalizeShake256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.finalizeShake256Reg,
  Spec.Sha3.squeezeShake256Api.artifact X86_64.target Proof.Sha3.X86_64.Scrub.squeezeShake256Reg]

end VG.Artifacts.Sha3.X86_64
