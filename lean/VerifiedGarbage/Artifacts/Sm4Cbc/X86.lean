module

public import VerifiedGarbage.Proof.Sm4.X86.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86.CbcLit

/-! # SM4-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcEncryptChained
    stack := 1516
    verified := Proof.Sm4.X86.Cbc.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 1496 4 368 Impl.Sm4.X86.cbcDecryptChained
    stack := 1516
    verified := Proof.Sm4.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.X86
