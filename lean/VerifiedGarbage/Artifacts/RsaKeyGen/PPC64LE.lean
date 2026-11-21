module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Scrub
public import VerifiedGarbage.Impl.RsaKeyGen.PPC64LE.Fn
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.Fn.keyInit
    verified := Proof.RsaKeyGen.PPC64LE.Scrub.keyInit_scrubbed }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map
    fun (vh : {v // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants}) =>
    Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target {
      suffix := vh.1.suffix
      code := Impl.RsaKeyGen.PPC64LE.Fn.keySearch vh.1.suffix vh.1.code
      verified := Proof.RsaKeyGen.PPC64LE.Scrub.keySearch_scrubbed vh.1 vh.2 })

end VG.Artifacts.RsaKeyGen.PPC64LE
