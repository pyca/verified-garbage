module

public import VerifiedGarbage.Proof.Blowfish.AArch64.KeyVerified
public import VerifiedGarbage.Proof.Blowfish.AArch64.Residue
public import VerifiedGarbage.Proof.Blowfish.AArch64.Frame
public import VerifiedGarbage.Proof.Blowfish.AArch64.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # Blowfish on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Blowfish.AArch64

def artifacts : List Artifact := [
  Spec.Blowfish.expandKeyApi.artifact AArch64.target {
    code := Proof.Blowfish.AArch64.expandKeyCleared
    verified := Proof.Blowfish.AArch64.expandKeyCleared_verified
    residue := some ⟨Proof.Blowfish.AArch64.expandKeyCleared_noResidue⟩ },
  Spec.Blowfish.ecbEncryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.encrypt
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.encrypt_verified },
  Spec.Blowfish.ecbDecryptApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 256 .x3 32 Impl.Blowfish.AArch64.decrypt
    verified := Proof.Blowfish.AArch64.ecb_framed Proof.Blowfish.AArch64.decrypt_verified }]

end VG.Artifacts.Blowfish.AArch64
