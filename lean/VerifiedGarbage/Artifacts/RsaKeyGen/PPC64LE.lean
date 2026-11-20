module

public import VerifiedGarbage.Proof.RsaKeyGen.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # RSA key generation (FIPS 186-5 A.1.3) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.RsaKeyGen.PPC64LE

def direct : List Artifact := [
  Spec.RsaKeyGen.keyInitApi.artifact PPC64LE.target {
    code := Impl.RsaKeyGen.PPC64LE.Fn.keyInit
    verified := .scrubbed Proof.RsaKeyGen.PPC64LE.Scrub.keyInit_scrubbed }]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.flatMap
    fun (v : { v : Proof.MillerRabin.PPC64LE.RoundImpl // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants }) => [
    Spec.RsaKeyGen.keySearchApi.artifact PPC64LE.target (Proof.RsaKeyGen.PPC64LE.Scrub.keySearchReg v.1 v.2)])

end VG.Artifacts.RsaKeyGen.PPC64LE
