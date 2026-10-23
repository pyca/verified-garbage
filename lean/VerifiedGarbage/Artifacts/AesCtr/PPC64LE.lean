module

public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-CTR (NIST SP 800-38A §6.5) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifacts it lists are
emitted. PPC64LE has one implementation of `vg_aes_ctr32`, so this is not
generic over it. A call (`bl`) stores nothing in memory, so no stack is
used.
-/

@[expose] public section

namespace VG.Artifacts.AesCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact PPC64LE.target {
    notes := [
      "This implementation calls `vg_aes_ctr32` on as many blocks at once as the counter's \
        last 32 bits allow, as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does."]
    code := Impl.AesCtr.PPC64LE.crypt
    verified := Proof.AesCtr.PPC64LE.crypt_verified }]

end VG.Artifacts.AesCtr.PPC64LE
