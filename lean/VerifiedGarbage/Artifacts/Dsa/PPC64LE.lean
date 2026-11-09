module

public import VerifiedGarbage.Proof.Dsa.PPC64LE.Params.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Derive.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.RandomSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Generate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Validate.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Prevalidated.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.PrevalidatedSign.Verified
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.PPC64LE.Print
public import VerifiedGarbage.Proof.Dsa.PPC64LE.Gen.Instances
public import VerifiedGarbage.Proof.Variants.MillerRabin.PPC64LE

/-! # DSA on PPC64LE -/

@[expose] public section

-- DSA parameter generation on PPC64LE, calling the probable-prime tests over each Miller–Rabin round
namespace VG.Artifacts.Dsa.PPC64LE.Parameters
open VG Proof.Dsa.PPC64LE.Gen

def artifactsFor (v : Proof.MillerRabin.PPC64LE.RoundImpl) : List Artifact := [
  Spec.Dsa.parameterSearchApi.artifact PPC64LE.target {
    suffix := v.suffix
    code := Impl.Dsa.PPC64LE.Generation.code (gen1 v) (gen2 v) (gen3 v)
    stack := 176
    verified := search_params v
    features := v.features }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MillerRabin.PPC64LE.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.Dsa.PPC64LE.Parameters

namespace VG.Artifacts.Dsa.PPC64LE

def artifacts : List Artifact := [
  Spec.Dsa.deriveKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Derive.derive
    verified := Proof.Dsa.PPC64LE.deriveKey_verified },
  Spec.Dsa.randomSignPrevalidatedApi.artifact PPC64LE.target {
    stack := 304
    code := Impl.Dsa.PPC64LE.RandomSign.code
    verified := Proof.Dsa.PPC64LE.randomSign_verified },
  Spec.Dsa.generateKeyApi.artifact PPC64LE.target {
    stack := 304
    code := Impl.Dsa.PPC64LE.Generate.code
    verified := Proof.Dsa.PPC64LE.generate_verified },
  Spec.Dsa.validatePublicKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Prevalidated.validate
    verified := Proof.Dsa.PPC64LE.validate_verified },
  Spec.Dsa.validatePrivateKeyApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.PrevalidatedSign.validate
    verified := Proof.Dsa.PPC64LE.validatePrivate_verified },
  Spec.Dsa.verifyPrevalidatedApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Prevalidated.verify
    verified := Proof.Dsa.PPC64LE.prevalidated_verified },
  Spec.Dsa.parameterInitApi.artifact PPC64LE.target {
    code := Impl.Dsa.PPC64LE.Generation.init
    verified := Proof.Dsa.PPC64LE.Gen.init_verified }] ++
  Parameters.artifacts

end VG.Artifacts.Dsa.PPC64LE
