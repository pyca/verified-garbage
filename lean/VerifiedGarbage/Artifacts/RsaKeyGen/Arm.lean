module

public import VerifiedGarbage.Proof.RsaKeyGen.Arm.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Rsa.Arm.InvLoop
public import VerifiedGarbage.TCB.Arm.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on ARMv7 -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.Arm

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact Arm.target {
    code := Impl.RsaKeyGen.Arm.KeyInit.init
    verified := Proof.RsaKeyGen.Arm.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.Arm
