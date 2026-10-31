module

public import VerifiedGarbage.Proof.AesOfb.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesOfb

open VG.Proof.AesOfb.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesOfb.X86.crypt v.enc
    stack := 24
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesOfb
