module

public import VerifiedGarbage.Proof.Sm4.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Sm4.X86_64.ModesLit

/-! # SM4-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.Sm4Cbc.X86_64

def artifacts : List Artifact := [
  Spec.Sm4.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcEncryptChained
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcEncryptChained_framed },
  Spec.Sm4.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3208 .r8 400 Impl.Sm4.X86_64.cbcDecryptChained
    stack := 3216
    verified := Proof.Sm4.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.Sm4Cbc.X86_64
