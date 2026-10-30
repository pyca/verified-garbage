module

public import VerifiedGarbage.Proof.Camellia.X86.CbcVerified
import VerifiedGarbage.Proof.Camellia.X86.CbcLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Camellia-CBC artifacts on baseline x86 (32-bit) -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcEncryptChained
    stack := 2772
    verified := Proof.Camellia.X86.Cbc.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86.target {
    code := Impl.StackScratch.X86.withStackScratchWiped 2756 5 682 Impl.Camellia.X86.cbcDecryptChained
    stack := 2772
    verified := Proof.Camellia.X86.Cbc.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.X86
