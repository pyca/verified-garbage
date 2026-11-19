module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # DSA (FIPS 186-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Dsa.PPC64LE

open VG Proof.Dsa.PPC64LE.Scrub

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target deriveKeyReg,
  Spec.Dsa.randomSignPrevalidatedApi.artifact PPC64LE.target randomSignPrevalidatedReg,
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target generateKeyReg,
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target validatePublicKeyReg,
  Spec.Dsa.validatePrivateKeyApi.artifact PPC64LE.target validatePrivateKeyReg,
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target verifyPrevalidatedReg,
  Spec.Dsa.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Generation.init
    verified := .scrubbed ⟨Proof.Dsa.PPC64LE.Gen.init_verified,
      Proof.Dsa.PPC64LE.Gen.init_noResidue _ _⟩ }] ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.flatMap
    fun (v : { v : Proof.MillerRabin.PPC64LE.RoundImpl // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants }) => [
    Spec.Dsa.parameterSearchApi.artifact PPC64LE.target (parameterSearchReg v.1 v.2)])

end VG.Artifacts.Dsa.PPC64LE
