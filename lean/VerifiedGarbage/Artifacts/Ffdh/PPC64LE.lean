module

public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Generation.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # Finite-field Diffie–Hellman (SP 800-56A) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Ffdh.PPC64LE

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.Generation.init
    verified := .scrubbed ⟨Proof.Ffdh.PPC64LE.Generation.init_verified,
      Proof.Ffdh.PPC64LE.Generation.init_noResidue _ _⟩ },
  Spec.Ffdh.keyInitApi.artifact PPC64LE.target {
    code := Impl.Ffdh.PPC64LE.KeyGeneration.init
    verified := .scrubbed ⟨Proof.Ffdh.PPC64LE.KeyGeneration.init_verified,
      Proof.Ffdh.PPC64LE.KeyGeneration.init_noResidue _ _⟩ },
  Spec.Ffdh.checkPublicApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.checkPublicReg,
  Spec.Ffdh.checkDomainApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.checkDomainReg,
  Spec.Ffdh.exchangeApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.exchangeReg,
  Spec.Ffdh.derivePublicApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.derivePublicReg,
  Spec.Ffdh.checkPrivateApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.checkPrivateReg,
  Spec.Ffdh.generationPrecomputeApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.precomputeReg,
  Spec.Ffdh.cachedKeySearchApi.artifact PPC64LE.target Proof.Ffdh.PPC64LE.Scrub.cachedKeySearchReg]

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map fun v =>
    Spec.Ffdh.sievedParameterSearchApi.artifact PPC64LE.target (Proof.Ffdh.PPC64LE.Scrub.searchReg v.1 v.2))

end VG.Artifacts.Ffdh.PPC64LE
