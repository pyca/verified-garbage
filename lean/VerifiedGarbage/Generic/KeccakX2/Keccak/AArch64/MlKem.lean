module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.KgH.Final
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.DecapsFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Inst
public import VerifiedGarbage.Proof.MlKem.AArch64.Kem16P.EncapsFinal
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration

/-! # ML-KEM-768 and ML-KEM-1024 (FIPS 203) on AArch64, for each Keccak implementation -/

@[expose] public section

namespace VG.Generic.KeccakX2.Keccak.AArch64.MlKem

open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prfW)
open VG.Proof.MlKem.AArch64.FixedHash.Inst (paired sponge parts features)

/-- One Keccak state at a time, over the sponge functions of `v`. -/
def spongeArtifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
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

/-- Paired sampling and fused arithmetic, calling `vg_keccak_f1600_x2_sha3`
(and, in `encaps` and `decaps`, `vg_keccak_f1600_x3_sha3`) and the single-state
permutation of `v` rather than the sponge functions. -/
def pairedArtifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) :
    List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768
    stack := 128
    verified := Proof.MlKem.AArch64.KeyGen.keyGenP768_verified v },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768
    stack := 128
    verified := Proof.MlKem.AArch64.Kem16P.encapsP768_verified v },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768
    stack := 128
    verified := Proof.MlKem.AArch64.Kem16P.decapsP768_verified v },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024
    stack := 128
    verified := Proof.MlKem.AArch64.KeyGen.keyGenP1024_verified v },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024
    stack := 128
    verified := Proof.MlKem.AArch64.Kem16P.encapsP1024_verified v },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024
    stack := 128
    verified := Proof.MlKem.AArch64.Kem16P.decapsP1024_verified v }]

def artifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if paired x2 then pairedArtifacts x2 v else if sponge x2 v then spongeArtifacts v else []

end VG.Generic.KeccakX2.Keccak.AArch64.MlKem
