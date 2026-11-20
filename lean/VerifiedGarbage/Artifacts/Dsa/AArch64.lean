module

public import VerifiedGarbage.Proof.Dsa.AArch64.ParameterSearchInit
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.Proof.Dsa.AArch64.Scrub
public import VerifiedGarbage.Proof.Dsa.AArch64.RandomSignVerified
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
    verified := .scrubbed Proof.Dsa.AArch64.ParameterSearchInit.init_scrubbed }]

end VG.Artifacts.Dsa.AArch64

namespace VG.Artifacts.Dsa.AArch64

open VG.Proof.Dsa.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.DsaArithmetic.AArch64.variants.flatMap fun (v : Backend) => [
    Spec.Dsa.randomSignPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.randomSignPrevalidated (prevalidatedSignerName v) v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.randomSignPrevalidated v) },
    Spec.Dsa.validatePrivateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.validatePrivateKey v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.validatePrivateKey v) },
    Spec.Dsa.validatePublicKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.validatePublicKey v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.validatePublicKey v) },
    Spec.Dsa.verifyPrevalidatedApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.verifyPrevalidated v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.verifyPrevalidated v) },
    Spec.Dsa.generateKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.generateKey (keygenCheckName v) (keygenDeriveName v) v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.generateKey v) },
    Spec.Dsa.deriveKeyApi.artifact AArch64.target {
      suffix := v.suffix
      code := Impl.Dsa.AArch64.Fn.deriveKey v.mul v.stack
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.deriveKey v) }]) ++
  (Generation.Refill.hashPairs.flatMap fun (p : Generation.Refill.Hashes) =>
    VG.Proof.Variants.MillerRabin.AArch64.variants.map fun (v : Proof.MillerRabin.AArch64.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact AArch64.target {
      suffix := qualifiedName "" [("sha1", p.sha1.suffix), ("sha256", p.sha256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.AArch64.Fn.parameterSearch p.sha1.H p.sha256.H v.suffix v.mont.mm v.roundMont.mm
      verified := .scrubbed (Proof.Dsa.AArch64.Scrub.parameterSearch p v) })

end VG.Artifacts.Dsa.AArch64
