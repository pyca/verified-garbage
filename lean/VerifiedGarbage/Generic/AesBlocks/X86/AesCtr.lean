module

public import VerifiedGarbage.Proof.AesCtr.X86.Verified
public import VerifiedGarbage.Proof.AesCtr.X86.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCtr

open VG.Proof.AesCtr.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
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

end VG.Generic.AesBlocks.X86.AesCtr
