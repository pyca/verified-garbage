module

public import VerifiedGarbage.Proof.AesOfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesOfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Aes.AArch64.ModesScrub
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.AArch64

/-! # AES-OFB (NIST SP 800-38A §6.4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.AArch64

open VG.Proof.AesOfb.AArch64

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.AArch64.variants.attach.flatMap
      fun (v : { v : Proof.Aes.AArch64.BlocksImpl // v ∈ VG.Proof.Variants.AesBlocks.AArch64.variants }) => [
    Spec.Ofb.aesApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.AesOfb.AArch64.crypt v.1.enc
      verified := Proof.AesOfb.keyed (crypt_verified v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.ofbOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.ofbOk (Proof.Aes.AArch64.ModesScrub.ofbSide v.1 v.2)),
    Spec.Ofb.aesFinalApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Impl.AesOfb.AArch64.cryptFinal v.1.enc v.1.suffix)
      verified := Proof.AesOfb.final_keyed (cryptFinal_framed v.1) }
      (AArch64.ScrubAll.clearUnion Proof.Aes.AArch64.ModesScrub.ofbFinalOwn v.1.encClear)
      Proof.Aes.AArch64.ModesScrub.ofbFinalOk (Proof.Aes.AArch64.ModesScrub.ofbFinalSide v.1 v.2))]

end VG.Artifacts.AesOfb.AArch64
