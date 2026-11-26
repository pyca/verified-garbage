module

public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
import VerifiedGarbage.Proof.Dsa.AArch64.ParameterSearchInit
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Dsa.AArch64.Scrub
import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
import VerifiedGarbage.Proof.Dsa.AArch64.GenerateKeyCorrect
import VerifiedGarbage.Proof.Variants.DsaArithmetic.AArch64
import VerifiedGarbage.Proof.Dsa.AArch64.Generation.RefillVerified
import VerifiedGarbage.Proof.Variants.MdHash.AArch64
import VerifiedGarbage.Proof.Variants.MillerRabin.AArch64
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # DSA (FIPS 186-4) on AArch64 -/

namespace VG.Artifacts.Dsa.AArch64

def direct : List (Artifact AArch64.target) := [
  Spec.Dsa.parameterInitApi.artifact AArch64.target {
    code := Impl.Dsa.AArch64.ParameterSearch.init
    verified := Proof.Dsa.AArch64.ParameterSearchInit.init_scrubbed
    publicOutOk := Proof.Dsa.AArch64.ParameterSearchInit.init_public }]

end VG.Artifacts.Dsa.AArch64

namespace VG.Artifacts.Dsa.AArch64

open VG.Proof.Dsa.AArch64

public def artifacts : List (Artifact AArch64.target) :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.AArch64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.randomSignPrevalidated (prevalidatedSignerName v) v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.randomSignPrevalidated v },
    Spec.Dsa.validatePrivateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.validatePrivateKey v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.validatePrivateKey v },
    Spec.Dsa.validatePublicKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.validatePublicKey v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.validatePublicKey v },
    Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.verifyPrevalidated v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.verifyPrevalidated v },
    Spec.Dsa.generateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.generateKey (keygenCheckName v) (keygenDeriveName v) v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.generateKey v },
    Spec.Dsa.deriveKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.deriveKey v.mul v.stack
      verified := Proof.Dsa.AArch64.Scrub.deriveKey v }]) ++
  (Generation.Refill.hashPairs.flatMap fun (p : Generation.Refill.Hashes) =>
    VG.Proof.Variants.MillerRabin.AArch64.variants.map fun (v : Proof.MillerRabin.AArch64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact AArch64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.AArch64.Fn.parameterSearch p.sha1.H p.sha256.H v.suffix v.mont.mm v.roundMont.mm
      verified := Proof.Dsa.AArch64.Scrub.parameterSearch p v
      publicOutOk := Proof.Dsa.AArch64.Scrub.parameterSearch_public p v })

spec_apis artifacts

end VG.Artifacts.Dsa.AArch64
