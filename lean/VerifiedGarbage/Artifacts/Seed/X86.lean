module

public import VerifiedGarbage.Proof.Seed.X86.KeyVerified
public import VerifiedGarbage.Proof.Seed.X86.Verified
public import VerifiedGarbage.Proof.Seed.X86.EcbCall
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86.Lit

/-! # SEED artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Seed.X86

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 840 2 206 Impl.Seed.X86.expandKey
    stack := 840
    verified := Proof.Seed.X86.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1108 3 272 (Impl.Seed.X86.ecbCall .encrypt)
    stack := 1132
    verified := Proof.Seed.X86.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1108 3 272 (Impl.Seed.X86.ecbCall .decrypt)
    stack := 1132
    verified := Proof.Seed.X86.ecbCall_framed .decrypt }]

end VG.Artifacts.Seed.X86
