module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Inv
public import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd2
public import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.AArch64.Decode12
public import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem.AArch64.Encode12
public import VerifiedGarbage.Proof.MlKem.AArch64.Mul
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Fwd
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.AArch64.Print
public import VerifiedGarbage.Proof.MlKem.AArch64.CallWipe
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.Inst
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Variants.KeccakX2.AArch64
public import VerifiedGarbage.Proof.Variants.Keccak.AArch64
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem1024.AArch64.DecodeDecompress
public import VerifiedGarbage.Proof.MlKem1024.AArch64.CheckEk

/-! # ML-KEM (FIPS 203) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.AArch64

def direct : List Artifact := [
  Spec.MlKem.checkEkApi.artifact AArch64.target {
    code := Impl.MlKem.AArch64.checkEk
    verified := Proof.MlKem.AArch64.CheckEk.checkEk_verified }]

end VG.Artifacts.MlKem.AArch64

-- ML-KEM-768 and ML-KEM-1024 (FIPS 203) on AArch64, for each Keccak implementation
namespace VG.Artifacts.MlKem.AArch64.KeccakX2Keccak

open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prfW)
open VG.Proof.MlKem.AArch64.FixedHash.Inst (paired parts)

/-- Paired sampling and fused arithmetic, calling the two- and three-state
functions of `x2` (`vg_keccak_f1600_x2` and `vg_keccak_f1600_x3`, or the
SHA-3 extension's) and the single-state permutation of `v`. -/
def pairedArtifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) :
    List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen x2.sha3 (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.keyGenP768_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.encapsP768_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem.encapsHApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.encapsHP768_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.decapsP768_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen x2.sha3 (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.keyGenP1024_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.encapsP1024_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem1024.encapsHApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.encapsHP1024_verified (sha3 := x2.sha3) v _ },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.decapsP1024_verified (sha3 := x2.sha3) v _ }]

/-- The functions over the two-state permutation `x2` and the single-state
one `v`, for every pair but the baseline `x2` with the SHA-3 `v` (`paired`). -/
def artifacts (x2 : Proof.Sha3.AArch64.X2Permutation) (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if paired x2 v then pairedArtifacts x2 v else []

end VG.Artifacts.MlKem.AArch64.KeccakX2Keccak

namespace VG.Artifacts.MlKem.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.KeccakX2.AArch64.variants.flatMap fun v => VG.Proof.Variants.Keccak.AArch64.variants.flatMap fun v2 => KeccakX2Keccak.artifacts v v2) ++
  [
    Spec.MlKem1024.checkEkApi.artifact AArch64.target {
      code := Impl.MlKem1024.AArch64.checkEk
      verified := Proof.MlKem1024.AArch64.CheckEk.checkEk_verified }]

end VG.Artifacts.MlKem.AArch64
