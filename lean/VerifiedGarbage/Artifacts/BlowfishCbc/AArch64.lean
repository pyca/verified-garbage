module

public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Blowfish-CBC artifacts on baseline AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcEncryptChained
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcEncryptChained_framed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 224 .x4 28 Impl.Blowfish.AArch64.cbcDecryptChained
    stack := 224
    verified := Proof.Blowfish.AArch64.cbcDecryptChained_framed }]

end VG.Artifacts.BlowfishCbc.AArch64
