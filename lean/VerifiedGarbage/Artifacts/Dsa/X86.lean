module

public import VerifiedGarbage.TCB.X86.Target
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Spec.Dsa.Generate
public import VerifiedGarbage.Spec.Dsa.Derive
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Spec.Dsa.Prevalidated
public import VerifiedGarbage.Spec.Dsa.ParameterSearchContract
import VerifiedGarbage.Proof.Dsa.X86.Scrub
import VerifiedGarbage.Impl.Dsa.X86.Fn
import VerifiedGarbage.Proof.Framework.Registration
import VerifiedGarbage.Proof.Variants.Sha1.X86
import VerifiedGarbage.Proof.Variants.Sha256.X86
import VerifiedGarbage.Proof.Variants.MillerRabin.X86
import VerifiedGarbage.Proof.Framework.QualifiedName
import VerifiedGarbage.Proof.Framework.SpecApis

/-! # DSA (FIPS 186-4) on x86 -/

namespace VG.Artifacts.Dsa.X86

open VG.Proof.Dsa.X86.Scrub

def direct : List (Artifact X86.target) := [
  Spec.Dsa.generateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.generateKey
    verified := Proof.Dsa.X86.Scrub.generateKey_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.generateKey_spSafe },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.deriveKey
    verified := Proof.Dsa.X86.Scrub.deriveKey_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.deriveKey_spSafe },
  Spec.Dsa.validatePrivateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.validatePrivateKey
    verified := Proof.Dsa.X86.Scrub.validatePrivateKey_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.validatePrivateKey_spSafe },
  Spec.Dsa.randomSignPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.randomSignPrevalidated
    verified := Proof.Dsa.X86.Scrub.randomSignPrevalidated_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.randomSignPrevalidated_spSafe },
  Spec.Dsa.validatePublicKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.validatePublicKey
    verified := Proof.Dsa.X86.Scrub.validatePublicKey_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.validatePublicKey_spSafe },
  Spec.Dsa.verifyPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.verifyPrevalidated
    verified := Proof.Dsa.X86.Scrub.verifyPrevalidated_scrubbed
    spSafe := Proof.Dsa.X86.Scrub.verifyPrevalidated_spSafe },
  Spec.Dsa.parameterInitApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.parameterInit
    verified := Proof.Dsa.X86.Scrub.parameterInit_scrubbed
    publicOutOk := Proof.Dsa.X86.Scrub.parameterInit_public
    spSafe := Proof.Dsa.X86.Scrub.parameterInit_spSafe }]

end VG.Artifacts.Dsa.X86

namespace VG.Artifacts.Dsa.X86

open VG.Proof.Dsa.X86.Generation (geo1 geo256)

public def artifacts : List (Artifact X86.target) :=
  direct ++
  (Proof.Dsa.X86.Generation.hashPairs.flatMap fun ((v1, v256) : Proof.Sha1.X86.Variants.Backend × Proof.Sha256.X86.Variants.Backend) =>
    VG.Proof.Variants.MillerRabin.X86.variants.map fun (v : Proof.MillerRabin.X86.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86.target {
      suffix := qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.X86.Fn.parameterSearch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
      verified := Proof.Dsa.X86.Scrub.parameterSearch_scrubbed v1 v256 v
      publicOutOk := Proof.Dsa.X86.Scrub.parameterSearch_public v1 v256 v
      spSafe := Proof.Dsa.X86.Scrub.parameterSearch_spSafe v1 v256 v })

spec_apis artifacts

end VG.Artifacts.Dsa.X86
