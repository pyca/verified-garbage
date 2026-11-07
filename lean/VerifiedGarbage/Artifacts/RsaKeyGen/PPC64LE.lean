module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def artifacts : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.KeyInit.init
    verified := Proof.RsaKeyGen.PPC64LE.KeyInit.init_verified }]

end VG.Artifacts.RsaKeyGen.PPC64LE
