module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.KeyInit
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.MillerRabin.PPC64LE.Backend
public import VerifiedGarbage.Impl.RsaKeyGen.TrialTable32
public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Rsa.PPC64LE.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.KeyInit.init
    verified := Proof.RsaKeyGen.PPC64LE.KeyInit.init_verified }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.flatMap fun (v : Proof.MillerRabin.PPC64LE.RoundImpl) => [
    Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target {
      suffix := v.suffix
      stack := 1088
      code := Proof.RsaKeyGen.PPC64LE.Generate.genCode v
      verified := Proof.RsaKeyGen.PPC64LE.Generate.gen_verified v }])

end VG.Artifacts.RsaKeyGen.PPC64LE
