module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Key.Verified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Instances
public import VerifiedGarbage.Proof.Framework.Registration

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.Key.code
    verified := Proof.RsaKeyGen.PPC64LE.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.PPC64LE
