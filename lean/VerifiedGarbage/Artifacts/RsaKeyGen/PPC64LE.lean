module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.RsaKeyGen.KeySearchContract
import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Scrub
import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def direct : List (Artifact PPC64LE.target) := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.Fn.keyInit
    verified := Proof.RsaKeyGen.PPC64LE.Scrub.keyInit_scrubbed
    publicOutOk := Proof.RsaKeyGen.PPC64LE.Scrub.keyInit_public }]

public def artifacts : List (Artifact PPC64LE.target) :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map
    fun (vh : {v // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants}) =>
    Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target {
      suffix := vh.1.suffix
      code := Impl.RsaKeyGen.PPC64LE.Fn.keySearch vh.1.suffix vh.1.code
      verified := Proof.RsaKeyGen.PPC64LE.Scrub.keySearch_scrubbed vh.1 vh.2
      publicOutOk := Proof.RsaKeyGen.PPC64LE.Scrub.keySearch_public vh.1 vh.2 })

spec_apis artifacts

end VG.Artifacts.RsaKeyGen.PPC64LE
