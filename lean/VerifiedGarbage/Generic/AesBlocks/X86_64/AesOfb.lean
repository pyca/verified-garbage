module

public import VerifiedGarbage.Proof.AesOfb.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-OFB (NIST SP 800-38A §6.4) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86_64.AesOfb

open VG.Proof.AesOfb.X86_64

def artifacts (v : Proof.Aes.X86_64.BlocksImpl) : List Artifact := [
  Spec.Ofb.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesOfb.X86_64.crypt v.enc
    stack := 8
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86_64.AesOfb
