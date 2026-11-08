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

/-! # DSA parameter search on AArch64 -/

@[expose] public section

namespace VG.Artifacts.Dsa.AArch64

def direct : List Artifact := [
  Spec.Dsa.parameterInitApi.artifact AArch64.target {
    code := Impl.Dsa.AArch64.ParameterSearch.init
    verified := Proof.Dsa.AArch64.ParameterSearchInit.init_verified }]

end VG.Artifacts.Dsa.AArch64

-- DSA signing and verification for every AArch64 arithmetic backend
namespace VG.Artifacts.Dsa.AArch64.DsaArithmetic
open VG.Proof.Dsa.AArch64

def artifacts (v : Backend) : List Artifact := [
  Spec.Dsa.randomSignPrevalidatedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.RandomSign.code (prevalidatedSignerName v)
      (Impl.Dsa.AArch64.PrevalidatedSign.sign v.mul)
    stack := v.stack + 256
    verified := random_sign_prevalidated_verified v
    spSafe := random_sign_sp v.prevalidatedSigner
    features := v.features },
  Spec.Dsa.validatePrivateKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.PrevalidatedSign.validate v.mul
    stack := v.stack
    verified := v.validatePrivateVerified
    spSafe := v.validatePrivateSp
    features := v.features },
  Spec.Dsa.validatePublicKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Prevalidated.validate v.mul
    stack := v.stack
    verified := v.validateVerified
    spSafe := v.validateSp
    features := v.features },
  Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Prevalidated.verify v.mul
    stack := v.stack
    verified := v.prevalidatedVerified
    spSafe := v.prevalidatedSp
    features := v.features },
  Spec.Dsa.generateKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.GenerateKey.code (keygenCheckName v) (keygenDeriveName v)
      (Impl.Dsa.AArch64.Generate.checkParameters v.mul) (Impl.Dsa.AArch64.Generate.deriveChecked v.mul)
    stack := v.stack + 256
    verified := keygen_verified v
    spSafe := keygen_sp v
    features := v.features },
  Spec.Dsa.deriveKeyApi.artifact AArch64.target {
    suffix := v.suffix
    code := Impl.Dsa.AArch64.Generate.deriveKey v.mul
    stack := v.stack
    verified := v.deriveVerified
    spSafe := v.deriveSp
    features := v.features }]

end VG.Artifacts.Dsa.AArch64.DsaArithmetic

-- DSA parameter generation over refillable tapes with every SHA-1, SHA-256 and Miller–Rabin backend on AArch64
namespace VG.Artifacts.Dsa.AArch64.MdHashMdHashMillerRabin

open VG.Proof.Dsa.AArch64.Generation VG.Proof.MillerRabin.AArch64

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines or both SHA-2 extensions), with each Miller–Rabin
round: either other pair needs the features of one of these, which runs
both hashes with them. -/
def artifacts (v1 v256 : Proof.Pbkdf2.Md.AArch64.MdHash) (v : RoundImpl) : List Artifact :=
  if v1.suffix != v256.suffix then [] else
  if h1 : v1.mgf.G.rust = "sha1" then
    if h256 : v256.mgf.G.rust = "sha256" then
      let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
      [Spec.Dsa.parameterSearchApi.artifact AArch64.target {
        suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
        stack := 768
        code := Impl.Dsa.AArch64.Generation.code v1.H v256.H (Proof.Dsa.AArch64.Generator.generatorStage v).run
          (Proof.Dsa.AArch64.ProbablePrime.primeTest v).run
        verified := Refill.backend_verified v1 v256 v h1 h256
        features := hashes ++ v.features.filter (!hashes.contains ·) }]
    else []
  else []

end VG.Artifacts.Dsa.AArch64.MdHashMdHashMillerRabin

namespace VG.Artifacts.Dsa.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.AArch64.variants.flatMap fun v => DsaArithmetic.artifacts v) ++
  (VG.Proof.Variants.MdHash.AArch64.variants.flatMap fun v => VG.Proof.Variants.MdHash.AArch64.variants.flatMap fun v2 => VG.Proof.Variants.MillerRabin.AArch64.variants.flatMap fun v3 => MdHashMdHashMillerRabin.artifacts v v2 v3)

end VG.Artifacts.Dsa.AArch64
