module

public import VerifiedGarbage.Proof.Seed.X86_64.Frame
public import VerifiedGarbage.Proof.Seed.X86_64.EcbCall
public import VerifiedGarbage.Proof.Seed.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Seed.X86_64.Lit

/-! # SEED artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Seed.X86_64

def artifacts : List Artifact := [
  Spec.Seed.expandKeyApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1064 .rdx 132 Impl.Seed.X86_64.expandKey
    stack := 1064
    verified := Proof.Seed.X86_64.expandKey_framed },
  Spec.Seed.ecbEncryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .encrypt)
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .encrypt },
  Spec.Seed.ecbDecryptApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 1096 .rcx 136 (Impl.Seed.X86_64.ecbCall .decrypt)
    stack := 1104
    verified := Proof.Seed.X86_64.ecbCall_framed .decrypt }]

end VG.Artifacts.Seed.X86_64
