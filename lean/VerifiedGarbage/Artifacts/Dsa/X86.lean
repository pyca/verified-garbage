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

/-! # DSA key generation, private-key validation and signing with a sampled nonce, verification, and the start of the parameter search, on baseline i686 -/

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

-- DSA parameter generation over refillable tapes on i686, for every SHA-1, SHA-256 and Miller–Rabin backend
namespace VG.Artifacts.Dsa.X86.Sha1Sha256MillerRabin
open VG VG.X86 VG.Proof.Dsa.X86.Generation VG.Proof.MillerRabin.X86

/-- DSA's parameter search for a SHA-1 and a SHA-256 backend for the same
CPUs (both baselines or both SHA extensions), with each Miller–Rabin round:
either other pair needs the features of one of these, which runs both
hashes with them. -/
def artifacts (v1 : Proof.Sha1.X86.Variants.Backend) (v256 : Proof.Sha256.X86.Variants.Backend) (v : RoundImpl) :
    List Artifact :=
  if v1.suffix != v256.suffix then [] else
  let hashes := v1.features ++ v256.features.filter (!v1.features.contains ·)
  [Spec.Dsa.parameterSearchApi.artifact target {
    suffix := Emit.qualifiedName "" [("sha1", v1.suffix), ("sha256", v256.suffix), ("mr", v.suffix)]
    code := Impl.Dsa.X86.Generation.code (geo1 v1 v) (geo256 256 v256 v) (geo256 384 v256 v)
    stack := 216
    verified := verified v1 v256 v
    spSafe := code_all v1 v256 v
    features := hashes ++ v.features.filter (!hashes.contains ·) }]

end VG.Artifacts.Dsa.X86.Sha1Sha256MillerRabin

namespace VG.Artifacts.Dsa.X86

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.Sha1.X86.variants.flatMap fun v => VG.Proof.Variants.Sha256.X86.variants.flatMap fun v2 => VG.Proof.Variants.MillerRabin.X86.variants.flatMap fun v3 => Sha1Sha256MillerRabin.artifacts v v2 v3)

end VG.Artifacts.Dsa.X86
