module

public import VerifiedGarbage.Proof.AesCtr.X86.Verified
public import VerifiedGarbage.Proof.AesCtr.X86.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86

open VG.Proof.AesCtr.X86

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86.crypt v.enc
    stack := 24
    verified := Proof.AesCtr.keyed (crypt_verified v)
    spSafe := crypt_spSafe v
    features := v.features },
  Spec.Ctr.aesFinalApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 64 6 8 (Impl.AesCtr.X86.cryptFinal v.enc v.suffix)
    stack := 116
    verified := Proof.AesCtr.final_keyed (cryptFinal_framed v)
    spSafe := cryptFinal_framed_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCtr.X86
