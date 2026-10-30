module

public import VerifiedGarbage.Proof.Camellia.X86_64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Camellia.X86_64.ModesLit

/-! # Camellia-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.CamelliaCbc.X86_64

def artifacts : List Artifact := [
  Spec.Camellia.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcEncryptChained
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcEncryptChained_framed },
  Spec.Camellia.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 3280 .r9 409 Impl.Camellia.X86_64.cbcDecryptChained
    stack := 3288
    verified := Proof.Camellia.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.CamelliaCbc.X86_64
