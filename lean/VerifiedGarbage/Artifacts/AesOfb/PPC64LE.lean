module

public import VerifiedGarbage.Proof.AesOfb.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-OFB (NIST SP 800-38A §6.4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesOfb.PPC64LE

def artifacts : List Artifact := [
  Spec.Ofb.aesApi.artifact PPC64LE.target {
    code := Impl.AesOfb.PPC64LE.crypt
    verified := Proof.AesOfb.PPC64LE.crypt_verified }]

end VG.Artifacts.AesOfb.PPC64LE
