module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Scrub
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # DSA (FIPS 186-4) on PPC64LE -/

@[expose] public section

namespace VG.Artifacts.Dsa.PPC64LE

open VG Proof.Dsa.PPC64LE.Scrub

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.deriveKey
    verified := deriveKey_scrubbed },
  Spec.Dsa.randomSignPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.randomSignPrevalidated
    verified := randomSignPrevalidated_scrubbed },
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.generateKey
    verified := generateKey_scrubbed },
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.validatePublicKey
    verified := validatePublicKey_scrubbed },
  Spec.Dsa.validatePrivateKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.validatePrivateKey
    verified := validatePrivateKey_scrubbed },
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Fn.verifyPrevalidated
    verified := verifyPrevalidated_scrubbed },
  Spec.Dsa.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Generation.init
    verified := parameterInit_scrubbed }] ++
  (VG.Proof.Variants.MillerRabin.PPC64LE.variants.attach.map fun ⟨v, hv⟩ =>
    Spec.Dsa.parameterSearchApi.artifact PPC64LE.target {
      suffix := v.suffix
      code := Impl.Dsa.PPC64LE.Fn.parameterSearch v.suffix v.code
      verified := Proof.Dsa.PPC64LE.Scrub.parameterSearch_scrubbed v hv })

end VG.Artifacts.Dsa.PPC64LE
