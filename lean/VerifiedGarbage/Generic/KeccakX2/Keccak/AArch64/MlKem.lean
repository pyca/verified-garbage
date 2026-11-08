module

public import VerifiedGarbage.Proof.MlKem.AArch64.CallWipe
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Inst
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print

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
    code := Impl.MlKem.AArch64.Wipe.keyGen v.callee.suffix (Impl.MlKem.AArch64.keyGenWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.keyGenS768_verified v },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.encaps v.callee.suffix (Impl.MlKem.AArch64.encapsWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.encapsS768_verified v },
  Spec.MlKem.encapsHApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.encapsH v.callee.suffix (Impl.MlKem.AArch64.encapsHWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.encapsHS768_verified v },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.decaps v.callee.suffix (Impl.MlKem.AArch64.decapsWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.decapsS768_verified v },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.keyGen1024 v.callee.suffix (Impl.MlKem1024.AArch64.keyGenWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.keyGenS1024_verified v },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.encaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.encapsS1024_verified v },
  Spec.MlKem1024.encapsHApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.encapsH1024 v.callee.suffix (Impl.MlKem1024.AArch64.encapsHWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.encapsHS1024_verified v },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.Wipe.decaps1024 v.callee.suffix (Impl.MlKem1024.AArch64.decapsWith v.callee)
    stack := 48
    verified := Proof.MlKem.AArch64.Wipe.decapsS1024_verified v }]

/-- Paired sampling and fused arithmetic, calling `vg_keccak_f1600_x2_sha3`
(and, in `encaps` and `decaps`, `vg_keccak_f1600_x3_sha3`) and the single-state
permutation of `v` rather than the sponge functions. -/
def pairedArtifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) :
    List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.keyGenP768_verified v _ },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.encapsP768_verified v _ },
  Spec.MlKem.encapsHApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.encapsHP768_verified v _ },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.decapsP768_verified v _ },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen1024 (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.keyGenP1024_verified v _ },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps1024 (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.encapsP1024_verified v _ },
  Spec.MlKem1024.encapsHApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH1024 (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.encapsHP1024_verified v _ },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := Emit.qualifiedName "" (parts x2 v)
    features := features x2 v
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps1024 (Emit.qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    stack := 160
    verified := Proof.MlKem.AArch64.Wipe.decapsP1024_verified v _ }]

def artifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if paired x2 then pairedArtifacts x2 v else if sponge x2 v then spongeArtifacts v else []

end VG.Generic.KeccakX2.Keccak.AArch64.MlKem
