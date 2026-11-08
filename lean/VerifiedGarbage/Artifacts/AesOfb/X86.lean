module

public import VerifiedGarbage.Proof.AesOfb.X86.Verified
public import VerifiedGarbage.Proof.AesOfb.X86.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.X86

open VG.Proof.AesOfb.X86

def artifactsFor (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesOfb.X86.crypt v.enc
    stack := 24
    verified := Proof.AesOfb.keyed (crypt_verified v)
    spSafe := crypt_spSafe v
    features := v.features },
  Spec.Ofb.aesFinalApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86.withStackScratchWiped 48 6 4 (Impl.AesOfb.X86.cryptFinal v.enc v.suffix)
    stack := 100
    verified := Proof.AesOfb.final_keyed (cryptFinal_framed v)
    spSafe := cryptFinal_framed_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesOfb.X86
