module

public import VerifiedGarbage.Proof.Sha512.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Sha512.X86.Lit

/-! # SHA-384, SHA-512, SHA-512/224 and SHA-512/256 (FIPS 180-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Sha512.X86

def artifacts : List Artifact := [
  Spec.Sha512.init384Api.artifact X86.target Proof.Sha512.X86.Scrub.init384Reg,
  Spec.Sha512.init512Api.artifact X86.target Proof.Sha512.X86.Scrub.init512Reg,
  Spec.Sha512.init512_224Api.artifact X86.target Proof.Sha512.X86.Scrub.init512_224Reg,
  Spec.Sha512.init512_256Api.artifact X86.target Proof.Sha512.X86.Scrub.init512_256Reg,
  Spec.Sha512.updateApi.artifact X86.target Proof.Sha512.X86.Scrub.updateReg,
  Spec.Sha512.finalizeApi.artifact X86.target Proof.Sha512.X86.Scrub.finalizeReg,
  Spec.Sha512.finalize384Api.artifact X86.target Proof.Sha512.X86.Scrub.finalize384Reg,
  Spec.Sha512.finalize512_256Api.artifact X86.target Proof.Sha512.X86.Scrub.finalize512_256Reg,
  Spec.Sha512.finalize512_224Api.artifact X86.target Proof.Sha512.X86.Scrub.finalize512_224Reg,
  Spec.Sha512.digest384Api.artifact X86.target Proof.Sha512.X86.Scrub.digest384Reg,
  Spec.Sha512.digest512Api.artifact X86.target Proof.Sha512.X86.Scrub.digest512Reg,
  Spec.Sha512.digest512_224Api.artifact X86.target Proof.Sha512.X86.Scrub.digest512_224Reg,
  Spec.Sha512.digest512_256Api.artifact X86.target Proof.Sha512.X86.Scrub.digest512_256Reg]

end VG.Artifacts.Sha512.X86
