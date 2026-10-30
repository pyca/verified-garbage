module

public import VerifiedGarbage.Proof.Seed.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.ModesLit

/-! # SEED-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.SeedCbc.X86_64

def artifacts : List Artifact := [
  Spec.Seed.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcEncryptChained
    stack := 1552
    verified := Proof.Seed.X86_64.cbcEncryptChained_framed },
  Spec.Seed.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1544 .r8 192 Impl.Seed.X86_64.cbcDecryptChained
    stack := 1552
    verified := Proof.Seed.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.SeedCbc.X86_64
