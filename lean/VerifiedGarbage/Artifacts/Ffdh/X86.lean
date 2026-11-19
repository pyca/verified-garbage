module

public import VerifiedGarbage.Proof.Ffdh.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86
open VG

def artifacts : List Artifact := [
  Spec.Ffdh.checkDomainApi.artifact X86.target Proof.Ffdh.X86.Scrub.checkDomainReg,
  Spec.Ffdh.checkPublicApi.artifact X86.target Proof.Ffdh.X86.Scrub.checkPublicReg,
  Spec.Ffdh.checkPrivateApi.artifact X86.target Proof.Ffdh.X86.Scrub.checkPrivateReg,
  Spec.Ffdh.exchangeApi.artifact X86.target Proof.Ffdh.X86.Scrub.exchangeReg,
  Spec.Ffdh.derivePublicApi.artifact X86.target Proof.Ffdh.X86.Scrub.derivePublicReg,
  Spec.Ffdh.keyInitApi.artifact X86.target Proof.Ffdh.X86.Scrub.keyInitReg,
  Spec.Ffdh.generationPrecomputeApi.artifact X86.target Proof.Ffdh.X86.Scrub.generationPrecomputeReg,
  Spec.Ffdh.cachedKeySearchApi.artifact X86.target Proof.Ffdh.X86.Scrub.cachedKeySearchReg,
  Spec.Ffdh.parameterInitApi.artifact X86.target Proof.Ffdh.X86.Scrub.parameterInitReg,
  Spec.Ffdh.sievedParameterSearchApi.artifact X86.target Proof.Ffdh.X86.Scrub.sievedParameterSearchReg]

end VG.Artifacts.Ffdh.X86
