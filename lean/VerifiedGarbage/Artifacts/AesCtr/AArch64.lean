module

public import VerifiedGarbage.Proof.AesCtr.AArch64.Verified
public import VerifiedGarbage.Proof.AesCtr.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.AArch64.ModesScrub
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64

/-! # AES-CTR (NIST SP 800-38A §6.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.AArch64

open VG.Proof.AesCtr.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Aes.AArch64.Ctr32Impl // v ∈ VG.Proof.Variants.AesCtr32.AArch64.variants }) => [
    Spec.Ctr.aesApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesCtr.AArch64.crypt v.1.callee
      verified := Proof.AesCtr.keyed (crypt_verified v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.ctrOwn v.1.clear)
      Proof.Aes.AArch64.ModesScrub.ctrOk (Proof.Aes.AArch64.ModesScrub.ctrSide v.1 v.2)),
    Spec.Ctr.aesFinalApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x6 10 (Impl.AesCtr.AArch64.cryptFinal v.1.callee v.1.suffix)
      verified := Proof.AesCtr.final_keyed (Final.cryptFinal_framed v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.ctrFinalOwn v.1.clear)
      Proof.Aes.AArch64.ModesScrub.ctrFinalOk (Proof.Aes.AArch64.ModesScrub.ctrFinalSide v.1 v.2))]

end VG.Artifacts.AesCtr.AArch64
