module

public import VerifiedGarbage.Proof.Dsa.X86.CheckingVerified
public import VerifiedGarbage.Proof.Dsa.X86.DerivingVerified
public import VerifiedGarbage.Spec.Dsa.PrevalidatedSign
public import VerifiedGarbage.Proof.Dsa.X86.ShapeCall
public import VerifiedGarbage.Proof.Dsa.X86.Comb.KeyVerified
public import VerifiedGarbage.Proof.Dsa.X86.Comb.PublicVerified
public import VerifiedGarbage.Proof.Dsa.X86.RandomSignInstance
public import VerifiedGarbage.Proof.Dsa.X86.PrevalidatedVerified
public import VerifiedGarbage.Proof.Dsa.X86.ValidatePrivateVerified
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Init
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.TCB.X86.Print
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Dsa.X86.Generation.Verified
public import VerifiedGarbage.Proof.Variants.Sha1.X86
public import VerifiedGarbage.Proof.Variants.Sha256.X86
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86
public import VerifiedGarbage.Proof.Framework.QualifiedName

/-! # DSA (FIPS 186-4) on x86 -/

@[expose] public section

namespace VG.Artifacts.Dsa.X86

def direct : List Artifact := [
  Spec.Dsa.generateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Comb.generateKey
    verified := Proof.Dsa.X86.Comb.key_verified
    stack := 232 },
  Spec.Dsa.deriveKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Generate.deriveKey
    verified := Proof.Dsa.X86.deriving_verified
    stack := 108 },
  Spec.Dsa.validatePrivateKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.PrevalidatedSign.validate
    verified := Proof.Dsa.X86.privateValidating_verified
    stack := 108 },
  Spec.Dsa.randomSignPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.RandomSign.code Proof.Dsa.X86.prevalidatedSignFn.name
      Proof.Dsa.X86.prevalidatedSignFn.code
    verified := Proof.Dsa.X86.randomSigningPrevalidated_verified
    stack := 232 },
  Spec.Dsa.validatePublicKeyApi.artifact X86.target {
    code := Impl.Dsa.X86.Prevalidated.validate
    verified := Proof.Dsa.X86.validating_verified
    stack := 108 },
  Spec.Dsa.verifyPrevalidatedApi.artifact X86.target {
    code := Impl.Dsa.X86.Prevalidated.verify
    verified := Proof.Dsa.X86.prevalidated_verified
    stack := 108 },
  Spec.Dsa.parameterInitApi.artifact X86.target {
    code := Impl.Dsa.X86.Generation.init
    verified := Proof.Dsa.X86.Generation.Init.init_verified }]

end VG.Artifacts.Dsa.X86

namespace VG.Artifacts.Dsa.X86

def artifacts : List Artifact :=
  direct ++
  (Proof.Dsa.X86.Generation.hashPairs.flatMap fun ((v1, v256) : Proof.Sha1.X86.Variants.Backend × Proof.Sha256.X86.Variants.Backend) =>
    VG.Proof.Variants.MillerRabin.X86.variants.map fun (v : Proof.MillerRabin.X86.RoundImpl) =>
    Spec.Dsa.parameterSearchApi.artifact X86.target {
      suffix := qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
      code := Impl.Dsa.X86.Generation.code (Proof.Dsa.X86.Generation.geo1 v1 v)
        (Proof.Dsa.X86.Generation.geo256 256 v256 v) (Proof.Dsa.X86.Generation.geo256 384 v256 v)
      stack := 216
      verified := Proof.Dsa.X86.Generation.verified v1 v256 v
      spSafe := Proof.Dsa.X86.Generation.code_all v1 v256 v })

end VG.Artifacts.Dsa.X86
