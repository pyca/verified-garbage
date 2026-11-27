module

public import VerifiedGarbage.TCB.PPC64LE.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.Proof.Dsa.PPC64LE.Scrub
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # DSA (FIPS 186-4) on PPC64LE -/

namespace VG.Artifacts.Dsa.PPC64LE

open VG Proof.Dsa.PPC64LE.Scrub

public def artifacts : List (Artifact PPC64LE.target) := [
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.deriveKey
    verified := Proof.Dsa.PPC64LE.Scrub.deriveKey_scrubbed },
  Spec.Dsa.randomSignPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.randomSignPrevalidated
    verified := Proof.Dsa.PPC64LE.Scrub.randomSignPrevalidated_scrubbed },
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.generateKey
    verified := Proof.Dsa.PPC64LE.Scrub.generateKey_scrubbed },
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.validatePublicKey
    verified := Proof.Dsa.PPC64LE.Scrub.validatePublicKey_scrubbed },
  Spec.Dsa.validatePrivateKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.validatePrivateKey
    verified := Proof.Dsa.PPC64LE.Scrub.validatePrivateKey_scrubbed },
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.verifyPrevalidated
    verified := Proof.Dsa.PPC64LE.Scrub.verifyPrevalidated_scrubbed },
  Spec.Dsa.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Generation.init
    verified := Proof.Dsa.PPC64LE.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Dsa.PPC64LE.Scrub.parameterInit_public }] ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map
    fun (vh : {v // v ∈ VG.Proof.Variants.MillerRabin.PPC64LE.variants}) =>
    Spec.Dsa.parameterSearchApi.artifact PPC64LE.target {
      suffix := vh.1.suffix
      code := Impl.Dsa.PPC64LE.Fn.parameterSearch vh.1.suffix vh.1.code
      verified := Proof.Dsa.PPC64LE.Scrub.parameterSearch_scrubbed vh.1 vh.2
      publicOutOk := Proof.Dsa.PPC64LE.Scrub.parameterSearch_public vh.1 vh.2 })

spec_apis artifacts

end VG.Artifacts.Dsa.PPC64LE
