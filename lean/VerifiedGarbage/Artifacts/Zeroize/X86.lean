module

public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.Zeroize.X86Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Zeroize.Common32
public import VerifiedGarbage.TCB.X86.Print

/-! # Zeroization on x86 -/

@[expose] public section

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target Proof.Zeroize.X86.zeroizeReg]
end VG.Artifacts.Zeroize.X86
