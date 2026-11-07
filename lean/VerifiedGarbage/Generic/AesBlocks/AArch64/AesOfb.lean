module

public import VerifiedGarbage.Proof.AesOfb.AArch64.Verified
public import VerifiedGarbage.Proof.AesOfb.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on AArch64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.AArch64.AesOfb

open VG.Proof.AesOfb.AArch64

def artifacts (v : Proof.Aes.AArch64.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesOfb.AArch64.crypt v.enc
    verified := Proof.AesOfb.keyed (crypt_verified v)
    features := v.features },
  Spec.Ofb.aesFinalApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratchWiped 64 .x6 8 (Impl.AesOfb.AArch64.cryptFinal v.enc v.suffix)
    stack := 64
    verified := Proof.AesOfb.final_keyed (cryptFinal_framed v)
    features := v.features }]

end VG.Generic.AesBlocks.AArch64.AesOfb
