module

public import VerifiedGarbage.Proof.Seed.X86.FbVerified
public import VerifiedGarbage.Proof.Seed.X86.FbFinalVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
import VerifiedGarbage.Proof.Seed.X86.FbLit
import VerifiedGarbage.Proof.Seed.X86.FbFinalLit

/-! # SEED-OFB artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedOfb.X86

def artifacts : List Artifact := [
  Spec.Seed.ofbApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.ofb
    stack := 1188
    verified := Proof.Seed.X86.Fb.ofb_framed },
  Spec.Seed.ofbFinalApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.ofbFinal
    stack := 1188
    verified := Proof.Seed.X86.FbFinal.ofbFinal_framed }]

end VG.Artifacts.SeedOfb.X86
