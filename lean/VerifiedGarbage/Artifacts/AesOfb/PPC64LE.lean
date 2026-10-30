module

public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-!
# AES-OFB (NIST SP 800-38A §6.4) on PPC64LE

A registration file (see `TCB/Emit.lean`): the artifact it lists is
emitted. PPC64LE has one implementation of the block functions, so this is
not generic over them. A call (`bl`) stores nothing in memory, so no stack is
used.
-/

@[expose] public section

namespace VG.Artifacts.AesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact PPC64LE.target {
    code := Impl.AesOfb.PPC64LE.crypt
    verified := Proof.AesOfb.PPC64LE.crypt_verified }]

end VG.Artifacts.AesOfb.PPC64LE
