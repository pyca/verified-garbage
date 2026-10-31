module

public import VerifiedGarbage.Proof.AesCtr.X86.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86 -/

@[expose] public section

namespace VG.Generic.AesBlocks.X86.AesCtr

open VG.Proof.AesCtr.X86

def artifacts (v : Proof.Aes.X86.BlocksImpl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86.crypt v.enc
    stack := 24
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesBlocks.X86.AesCtr
