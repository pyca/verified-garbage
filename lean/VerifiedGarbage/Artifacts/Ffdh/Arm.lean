module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInitVerified
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterInitVerified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Arm.Print
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Spec.Ffdh.GenerationContract
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Verified
public import VerifiedGarbage.Spec.Ffdh.SievedContract
public import VerifiedGarbage.Proof.Variants.MillerRabin.Arm
public import VerifiedGarbage.Proof.Bignum.Arm.MontBackend
public import VerifiedGarbage.Proof.Variants.RsaMont.Arm

/-! # Native FFDH on little-endian AAPCS ARMv7, including baseline and UMAAL arithmetic -/

@[expose] public section

namespace VG.Artifacts.Ffdh.Arm
open VG

def direct : List Artifact :=
  [
    Spec.Ffdh.keyInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.KeyGeneration.init
      verified := Proof.Ffdh.Arm.keyInit_verified },
    Spec.Ffdh.parameterInitApi.artifact VG.Arm.target {
      code := Impl.Ffdh.Arm.Generation.init
      verified := Proof.Ffdh.Arm.parameterInit_verified }]

end VG.Artifacts.Ffdh.Arm

-- Emit complete native FFDH parameter generation for every shared ARMv7 Miller–Rabin backend
namespace VG.Artifacts.Ffdh.Arm.MillerRabin
open VG

def artifacts (v : Proof.MillerRabin.Arm.RoundImpl) : List Artifact :=
  let b := Proof.Ffdh.Arm.parameterBackend v
  [Spec.Ffdh.sievedParameterSearchApi.artifact VG.Arm.target {
    suffix := b.suffix
    features := b.features
    stack := 232
    code := Impl.Ffdh.Arm.ParameterSearch.code (.call b.candidateName b.candidate)
    verified := Proof.Ffdh.Arm.ParameterSearch.verified b }]

end VG.Artifacts.Ffdh.Arm.MillerRabin

-- ARM key-generation artifacts are emitted by CachedFfdh
namespace VG.Artifacts.Ffdh.Arm.RsaMont
open VG

def artifacts (_v : Proof.Bignum.Arm.MontBackend) : List Artifact := []

end VG.Artifacts.Ffdh.Arm.RsaMont

namespace VG.Artifacts.Ffdh.Arm

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.MillerRabin.Arm.variants.flatMap fun v => MillerRabin.artifacts v) ++
  (VG.Proof.Variants.RsaMont.Arm.variants.flatMap fun v => RsaMont.artifacts v)

end VG.Artifacts.Ffdh.Arm
