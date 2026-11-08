module

public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.AesCtr.X86_64.Final
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.AesCtr32.X86_64

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.AesCtr.X86_64

open VG.Proof.AesCtr.X86_64

def artifactsFor (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86_64.crypt v.callee
    stack := 8
    verified := Proof.AesCtr.keyed (crypt_verified v)
    spSafe := crypt_spSafe v
    features := v.features },
  Spec.Ctr.aesFinalApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.StackScratch.X86_64.withStackArgScratchWiped 80 0 8 (Impl.AesCtr.X86_64.cryptFinal v.callee v.suffix)
    stack := 96
    verified := Proof.AesCtr.final_keyed (cryptFinal_framed v)
    spSafe := cryptFinal_framed_spSafe v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.AesCtr32.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.AesCtr.X86_64
