module

public import VerifiedGarbage.Proof.Zeroize.X86
public import VerifiedGarbage.Proof.Zeroize.X86Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Zeroize.Common32
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Impl.Zeroize.X86

/-! # Zeroization on x86 -/

@[expose] public section

namespace VG.Artifacts.Zeroize.X86
open VG.X86

def artifacts : List Artifact := [
  Spec.Zeroize.zeroizeApi.artifact target {
    code := Impl.Zeroize.X86.Fn.zeroize
    verified := Proof.Zeroize.X86.zeroize_scrubbed }]
end VG.Artifacts.Zeroize.X86
