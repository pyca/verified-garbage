module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.Key.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.Arm.InvLoop

/-! # RSA key generation (FIPS 186-5 A.1.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.Arm

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyApi.artifact Arm.target {
    code := Impl.RsaKeyGen.Arm.Key.code
    stack := 56
    verified := Proof.RsaKeyGen.Arm.Key.key_verified }]

end VG.Artifacts.RsaKeyGen.Arm
