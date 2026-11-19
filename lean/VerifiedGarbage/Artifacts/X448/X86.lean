module

public import VerifiedGarbage.Proof.X448.X86.Verified
public import VerifiedGarbage.Proof.X448.X86.Base
public import VerifiedGarbage.Proof.Ed448.CombFacts
import VerifiedGarbage.Proof.X448.X86.Lit
public import VerifiedGarbage.Proof.X448.X86.Exchange
public import VerifiedGarbage.Proof.X448.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # X448 (RFC 7748) on x86 -/

@[expose] public section

namespace VG.Artifacts.X448.X86

def artifacts : List Artifact := [
  Spec.X448.exchangeApi.artifact X86.target Proof.X448.X86.Scrub.exchangeReg,
  Spec.X448.x448BaseApi.artifact X86.target Proof.X448.X86.Scrub.baseReg]

end VG.Artifacts.X448.X86
