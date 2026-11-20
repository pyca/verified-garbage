module

public import VerifiedGarbage.Proof.Dsa.X86.Scrub
public import VerifiedGarbage.Impl.Dsa.X86.Fn
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # DSA (FIPS 186-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

open VG.Proof.Dsa.X86.Scrub

def direct : List Artifact := [
  Spec.Dsa.generateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.generateKey
    verified := .scrubbed generateKey_scrubbed
    spSafe := generateKey_spSafe },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.deriveKey
    verified := .scrubbed deriveKey_scrubbed
    spSafe := deriveKey_spSafe },
  Spec.Dsa.validatePrivateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.validatePrivateKey
    verified := .scrubbed validatePrivateKey_scrubbed
    spSafe := validatePrivateKey_spSafe },
  Spec.Dsa.randomSignPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.randomSignPrevalidated
    verified := .scrubbed randomSignPrevalidated_scrubbed
    spSafe := randomSignPrevalidated_spSafe },
  Spec.Dsa.validatePublicKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.validatePublicKey
    verified := .scrubbed validatePublicKey_scrubbed
    spSafe := validatePublicKey_spSafe },
  Spec.Dsa.verifyPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.verifyPrevalidated
    verified := .scrubbed verifyPrevalidated_scrubbed
    spSafe := verifyPrevalidated_spSafe },
  Spec.Dsa.parameterInitApi.artifact X86.target {
    code := Impl.Dsa.X86.Fn.parameterInit
    verified := .scrubbed parameterInit_scrubbed
    spSafe := parameterInit_spSafe }]

end VG.Artifacts.Dsa.X86

namespace VG.Artifacts.Dsa.X86

open VG.Proof.Dsa.X86.Generation (geo1 geo256)

def artifacts : List Artifact :=
  direct ++
  (Proof.Dsa.X86.Generation.hashPairs.flatMap fun ((v1, v256) : Proof.Sha1.X86.Variants.Backend × Proof.Sha256.X86.Variants.Backend) =>
    VG.Proof.Variants.MillerRabin.X86.variants.map fun (v : Proof.MillerRabin.X86.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86.target {
      suffix := qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.X86.Fn.parameterSearch (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
      verified := .scrubbed (Proof.Dsa.X86.Scrub.parameterSearch_scrubbed v1 v256 v)
      spSafe := Proof.Dsa.X86.Scrub.parameterSearch_spSafe v1 v256 v })

end VG.Artifacts.Dsa.X86
