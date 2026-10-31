module

public import VerifiedGarbage.Proof.AesCtr.X86_64.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CTR (NIST SP 800-38A §6.5) on x86-64 -/

@[expose] public section

namespace VG.Generic.AesCtr32.X86_64.AesCtr

open VG.Proof.AesCtr.X86_64

def artifacts (v : Proof.Aes.X86_64.Ctr32Impl) : List Artifact := [
  Spec.Ctr.aesApi.artifact X86_64.target {
    suffix := v.suffix
    code := Impl.AesCtr.X86_64.crypt v.callee
    stack := 8
    verified := crypt_verified v
    spSafe := crypt_spSafe v
    features := v.features }]

end VG.Generic.AesCtr32.X86_64.AesCtr
