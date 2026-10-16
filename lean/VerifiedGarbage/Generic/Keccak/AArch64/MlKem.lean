module

import VerifiedGarbage.Proof.MlKem.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem.AArch64.Encaps
import VerifiedGarbage.Proof.MlKem.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.Optimized.Verified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsVerified
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

/-! `keygen`, `encaps` and `decaps` of ML-KEM-768 and ML-KEM-1024, for each
Keccak implementation: the same code and proofs, for each parameter set. -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlKem

def legacyArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.keyGenWith v.callee
    stack := 16
    verified := Proof.MlKem.AArch64.KeyGen.keyGen_verifiedWith (keccak := v) },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.encapsWith v.callee
    stack := 16
    verified := Proof.MlKem.AArch64.Encaps.encaps_verifiedWith (keccak := v) },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.decapsWith v.callee
    stack := 16
    verified := Proof.MlKem.AArch64.Decaps.decaps_verifiedWith (keccak := v) },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem1024.AArch64.keyGenWith v.callee
    stack := 16
    verified := Proof.MlKem1024.AArch64.KeyGen.keyGen_verifiedWith (keccak := v) },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem1024.AArch64.encapsWith v.callee
    stack := 16
    verified := Proof.MlKem1024.AArch64.Encaps.encaps_verifiedWith (keccak := v) },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem1024.AArch64.decapsWith v.callee
    stack := 16
    verified := Proof.MlKem1024.AArch64.Decaps.decaps_verifiedWith (keccak := v) }]

/-- Paired sampling and fused arithmetic for the hardware SHA3 backend. -/
def optimizedArtifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem.AArch64.lay768
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen768_final },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Optimized.encapsUsing (Impl.MlKem.AArch64.FixedHashCallers.enAUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem.AArch64.lay768) Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.encaps768_verified },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps768_verified },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem1024.AArch64.lay1024
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen1024_final },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Optimized.encapsUsing (Impl.MlKem.AArch64.FixedHashCallers.enAUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem1024.AArch64.lay1024) Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.encaps1024_verified },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := "_paired_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps1024_verified }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  legacyArtifacts v ++ if v.callee.pairedSha3 then optimizedArtifacts else []

end VG.Generic.Keccak.AArch64.MlKem
