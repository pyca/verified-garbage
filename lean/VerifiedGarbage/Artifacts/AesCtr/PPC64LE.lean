module

public import VerifiedGarbage.Proof.AesCtr.PPC64LE.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # AES-CTR (NIST SP 800-38A §6.5) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.AesCtr.PPC64LE

def artifacts : List Artifact := [
  Spec.Ctr.aesApi.artifact PPC64LE.target {
    code := Impl.AesCtr.PPC64LE.crypt
    verified := Proof.AesCtr.PPC64LE.crypt_verified }]

end VG.Artifacts.AesCtr.PPC64LE
