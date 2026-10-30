module

public import VerifiedGarbage.Proof.Seed.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.CbcLit

/-! # SEED-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcEncryptChained
    stack := 1188
    verified := Proof.Seed.X86.Cbc.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1168 4 286 Impl.Seed.X86.cbcDecryptChained
    stack := 1188
    verified := Proof.Seed.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.X86
