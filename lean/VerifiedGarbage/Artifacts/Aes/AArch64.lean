module

public import VerifiedGarbage.Proof.Aes.AArch64.Aese.ExpandKey
public import VerifiedGarbage.Proof.Aes.AArch64.Frame
public import VerifiedGarbage.Proof.Aes.AArch64.ExpandKey
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES (FIPS 197) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Aes.AArch64

def artifacts : List Artifact := [
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64 Impl.Aes.AArch64.expandKey
    stack := 512
    verified := Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.expandKey_verified },
  Spec.Aes.expandKeyApi.artifact AArch64.target {
    suffix := "_aes"
    code := Impl.StackScratch.AArch64.withStackScratchWiped 512 .x3 64
      Impl.Aes.AArch64.Aese.expandKey
    stack := 512
    verified := Proof.Aes.AArch64.expandKey_framed Proof.Aes.AArch64.Aese.Key.expandKey_verified }]

end VG.Artifacts.Aes.AArch64
