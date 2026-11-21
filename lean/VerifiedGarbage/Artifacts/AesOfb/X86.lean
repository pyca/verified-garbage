module

public import VerifiedGarbage.Impl.AesOfb.X86.Final
public import VerifiedGarbage.Proof.AesOfb.X86.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Variants.AesBlocks.X86

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86 -/

@[expose] public section

namespace VG.Artifacts.AesOfb.X86

def artifacts : List Artifact :=
  VG.Proof.Variants.AesBlocks.X86.variants.flatMap fun (v : Proof.Aes.X86.BlocksImpl) => [
    Spec.Ofb.aesApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86.Fn.crypt v.enc
      verified := Proof.AesOfb.X86.Scrub.ofb_scrubbed v
      spSafe := Proof.AesOfb.X86.Scrub.ofb_fnSpSafe v },
    Spec.Ofb.aesFinalApi.artifact X86.target {
      suffix := v.suffix
      code := Impl.AesOfb.X86.Fn.cryptFinal v.enc v.suffix
      verified := Proof.AesOfb.X86.Scrub.ofbFinal_scrubbed v
      spSafe := Proof.AesOfb.X86.Scrub.ofbFinal_fnSpSafe v }]

end VG.Artifacts.AesOfb.X86
