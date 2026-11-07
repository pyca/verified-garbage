module

public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.AesOfb.X86_64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesOfb

open VG.Proof.AesOfb.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesOfb.X86_64.crypt v.enc
    stack := 8
    verified := Proof.AesOfb.keyed (crypt_verified v)
    spSafe := crypt_spSafe v
    features := v.features },
  Spec.Ofb.aesFinalApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 64 0 6 (Impl.AesOfb.X86_64.cryptFinal v.enc v.suffix)
    stack := 80
    verified := Proof.AesOfb.final_keyed (cryptFinal_framed v)
    spSafe := cryptFinal_framed_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOfb
