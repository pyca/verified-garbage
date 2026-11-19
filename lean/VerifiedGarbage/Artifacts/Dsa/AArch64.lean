module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.AArch64.Scrub
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignCode
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyVerified
public import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
public import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64
public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillVerified
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Variants.MdHash.AArch64
public import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # DSA (FIPS 186-4) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.AArch64

def direct : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact AArch64.target {
    code := Impl.Dsa.AArch64.ParameterSearch.init
    verified := Proof.Dsa.AArch64.ParameterSearchInit.init_verified
    residue := some ⟨Proof.Dsa.AArch64.ParameterSearchInit.init_noResidue _ _⟩ }]

end VG.Artifacts.Dsa.AArch64

namespace VG.Artifacts.Dsa.AArch64

open VG.Proof.Dsa.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.AArch64.variants.attach.flatMap fun (v : { v : Backend // v ∈ _ }) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.RandomSign.code (prevalidatedSignerName v.1)
        (Impl.Dsa.AArch64.PrevalidatedSign.sign v.1.mul)
      verified := random_sign_prevalidated_verified v.1
      spSafe := random_sign_sp v.1.prevalidatedSigner } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.randomSignPrevalidatedOk _) (Proof.Dsa.AArch64.Scrub.randomSignPrevalidatedSide v.1 v.2)),
    Spec.Dsa.validatePrivateKeyApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.PrevalidatedSign.validate v.1.mul
      verified := v.1.validatePrivateVerified
      spSafe := v.1.validatePrivateSp } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.validatePrivateKeyOk _) (Proof.Dsa.AArch64.Scrub.validatePrivateKeySide v.1 v.2)),
    Spec.Dsa.validatePublicKeyApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.Prevalidated.validate v.1.mul
      verified := v.1.validateVerified
      spSafe := v.1.validateSp } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.validatePublicKeyOk _) (Proof.Dsa.AArch64.Scrub.validatePublicKeySide v.1 v.2)),
    Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.Prevalidated.verify v.1.mul
      verified := v.1.prevalidatedVerified
      spSafe := v.1.prevalidatedSp } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.verifyPrevalidatedOk _) (Proof.Dsa.AArch64.Scrub.verifyPrevalidatedSide v.1 v.2)),
    Spec.Dsa.generateKeyApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v.1) (keygenDeriveName v.1)
        (Impl.Dsa.AArch64.Generate.checkParameters v.1.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.1.mul)
      verified := keygen_verified v.1
      spSafe := keygen_sp v.1 } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.generateKeyOk _) (Proof.Dsa.AArch64.Scrub.generateKeySide v.1 v.2)),
    Spec.Dsa.deriveKeyApi.artifact AArch64.target (VG.AArch64.ScrubAll.scrubAllOf {
      suffix := v.1.suffix
      code := Impl.Dsa.AArch64.Generate.deriveKey v.1.mul
      verified := v.1.deriveVerified
      spSafe := v.1.deriveSp } Proof.Dsa.AArch64.Scrub.clear
      (Proof.Dsa.AArch64.Scrub.deriveKeyOk _) (Proof.Dsa.AArch64.Scrub.deriveKeySide v.1 v.2))]) ++
  (Generation.Refill.hashPairs.flatMap fun (p : Generation.Refill.Hashes) =>
    VG.Proof.Variants.MillerRabin.AArch64.variants.map fun (v : Proof.MillerRabin.AArch64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact AArch64.target (VG.AArch64.ScrubAll.withScrubAll {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.AArch64.Generation.code p.sha1.H p.sha256.H (Generator.generatorStage v).run
        (ProbablePrime.primeTest v).run
      verified := Generation.Refill.backend_verified p.sha1 p.sha256 v p.h1 p.h256 } (Proof.Dsa.AArch64.Scrub.parameterSearchOk _)))

end VG.Artifacts.Dsa.AArch64
