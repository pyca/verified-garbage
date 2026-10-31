module

public import VerifiedGarbage.Proof.Blowfish.X86_64.CbcVerified
import VerifiedGarbage.Proof.Blowfish.X86_64.ModesLit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline x86-64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.X86_64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcEncryptChained
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact X86_64.target {
    code := Impl.StackScratch.X86_64.withStackScratchWiped 96 .r8 11 Impl.Blowfish.X86_64.cbcDecryptChained
    stack := 96
    verified := Proof.Blowfish.X86_64.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.X86_64
