module

public import VerifiedGarbage.Proof.AesCtr.AArch64.Verified
public import VerifiedGarbage.Proof.AesCtr.AArch64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.AArch64

/-! # AES-CTR (NIST SP 800-38A §6.5) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.AArch64

open VG.Proof.AesCtr.AArch64

def artifactsFor (v : Proof.Aes.AArch64.Ctr32Impl) : List Artifact := [
  Spec.Ctr.aesApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.AesCtr.AArch64.crypt v.callee
    verified := Proof.AesCtr.keyed (crypt_verified v)
    features := v.features },
  Spec.Ctr.aesFinalApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.StackScratch.AArch64.withStackScratchWiped 80 .x6 10 (Impl.AesCtr.AArch64.cryptFinal v.callee v.suffix)
    stack := 80
    verified := Proof.AesCtr.final_keyed (Final.cryptFinal_framed v)
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.AArch64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCtr.AArch64
