module

public import VerifiedGarbage.Impl.Blowfish.AArch64.Fn
public import VerifiedGarbage.Proof.Blowfish.AArch64.CbcVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.ModesResidue
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Blowfish-CBC on AArch64 -/

@[expose] public section

namespace VG.Artifacts.BlowfishCbc.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.cbcEncryptChainedApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cbcEncryptChained
    verified := Proof.Blowfish.AArch64.ModesResidue.cbcEncryptChainedCode_scrubbed },
  Spec.Blowfish.cbcDecryptChainedApi.artifact AArch64.target {
    code := Impl.Blowfish.AArch64.Fn.cbcDecryptChained
    verified := Proof.Blowfish.AArch64.ModesResidue.cbcDecryptChainedCode_scrubbed }]

end VG.Artifacts.BlowfishCbc.AArch64
