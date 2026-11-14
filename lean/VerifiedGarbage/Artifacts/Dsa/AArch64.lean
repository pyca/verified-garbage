module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Framework.Registration
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
    verified := Proof.Dsa.AArch64.ParameterSearchInit.init_verified }]

end VG.Artifacts.Dsa.AArch64

namespace VG.Artifacts.Dsa.AArch64

open VG.Proof.Dsa.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.AArch64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.RandomSign.code (prevalidatedSignerName v)
        (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul)
      stack := v.stack + 256
      verified := random_sign_prevalidated_verified v
      spSafe := random_sign_sp v.prevalidatedSigner },
    Spec.Dsa.validatePrivateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul
      stack := v.stack
      verified := v.validatePrivateVerified
      spSafe := v.validatePrivateSp },
    Spec.Dsa.validatePublicKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Prevalidated.validate v.mul
      stack := v.stack
      verified := v.validateVerified
      spSafe := v.validateSp },
    Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Prevalidated.verify v.mul
      stack := v.stack
      verified := v.prevalidatedVerified
      spSafe := v.prevalidatedSp },
    Spec.Dsa.generateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
        (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul)
      stack := v.stack + 256
      verified := keygen_verified v
      spSafe := keygen_sp v },
    Spec.Dsa.deriveKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Generate.deriveKey v.mul
      stack := v.stack
      verified := v.deriveVerified
      spSafe := v.deriveSp }]) ++
  (Generation.Refill.hashPairs.flatMap fun (p : Generation.Refill.Hashes) =>
    VG.Proof.Variants.MillerRabin.AArch64.variants.map fun (v : Proof.MillerRabin.AArch64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact AArch64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      stack := 768
      code := Impl.Dsa.AArch64.Generation.code p.sha1.H p.sha256.H (Generator.generatorStage v).run
        (ProbablePrime.primeTest v).run
      verified := Generation.Refill.backend_verified p.sha1 p.sha256 v p.h1 p.h256 })

end VG.Artifacts.Dsa.AArch64
