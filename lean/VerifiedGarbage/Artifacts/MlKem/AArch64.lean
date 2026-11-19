module

public import VerifiedGarbage.Proof.MlKem.AArch64.CheckEk
public import VerifiedGarbage.Proof.MlKem.AArch64.AddSub
public import VerifiedGarbage.Proof.MlKem.AArch64.CompressEncode
public import VerifiedGarbage.Proof.MlKem.AArch64.DecodeDecompress
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
public import VerifiedGarbage.Impl.MlKem.AArch64.Ntt16
public import VerifiedGarbage.Proof.MlKem.AArch64.NttCommon
public import VerifiedGarbage.Impl.MlKem.AArch64.Encode
public import VerifiedGarbage.Proof.MlKem.AArch64.Cbd16.Base
public import VerifiedGarbage.TCB.AArch64.Target
public import VerifiedGarbage.Proof.MlKem.AArch64.Codec16.DecBase
public import VerifiedGarbage.Proof.MlKem.Mem
public import VerifiedGarbage.TCB.AArch64.Isa
public import VerifiedGarbage.Proof.MlKem.AArch64.Common
public import VerifiedGarbage.Proof.MlKem.AArch64.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Ntt16.Vec
public import VerifiedGarbage.Proof.MlKem.AArch64.Residue
public import VerifiedGarbage.Proof.MlKem.AArch64.Scrub

/-! # ML-KEM (FIPS 203) on AArch64 -/

@[expose] public section

namespace VG.Artifacts.MlKem.AArch64

def direct : List Artifact := [
  Spec.MlKem.checkEkApi.artifact AArch64.target {
    code := Proof.MlKem.AArch64.Residue.checkEk768Cleared
    verified := .scrubbed ⟨Proof.MlKem.AArch64.Residue.checkEk768Cleared_verified,
      Proof.MlKem.AArch64.Residue.checkEk768Cleared_noResidue _⟩ }]

end VG.Artifacts.MlKem.AArch64

-- ML-KEM-768 and ML-KEM-1024 (FIPS 203) on AArch64, for each Keccak implementation
namespace VG.Artifacts.MlKem.AArch64.KeccakX2Keccak

open VG.Proof.MlKem.AArch64.FixedHash (fixedHash prfW)
open VG.Proof.MlKem.AArch64.FixedHash.Inst (paired parts)

/-- Paired sampling and fused arithmetic, calling the two- and three-state
functions of `x2` (`vg_keccak_f1600_x2` and `vg_keccak_f1600_x3`, or the
SHA-3 extension's) and the single-state permutation of `v`. -/
def pairedArtifacts (x2 : Proof.Sha3.AArch64.X2Permutation)
    (hx2 : x2 ∈ VG.Proof.Variants.KeccakX2.AArch64.variants) (v : Proof.Sha3.AArch64.Permutation)
    (hv : v ∈ VG.Proof.Variants.Keccak.AArch64.variants) : List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen x2.sha3 (fixedHash v.callee) v.callee Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.keyGenP768_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.keyGenOk_tables 160) (Proof.MlKem.AArch64.Scrub.keyGenSide x2 hx2 v hv)),
  Spec.MlKem.encapsApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.encapsP768_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.encapsOk_tables 160) (Proof.MlKem.AArch64.Scrub.encapsSide x2 hx2 v hv)),
  Spec.MlKem.encapsHApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.encapsHP768_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.encapsHOk_tables 160) (Proof.MlKem.AArch64.Scrub.encapsHSide x2 hx2 v hv)),
  Spec.MlKem.decapsApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem.AArch64.lay768)
    verified := Proof.MlKem.AArch64.Wipe.decapsP768_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.decapsOk_tables 160) (Proof.MlKem.AArch64.Scrub.decapsSide x2 hx2 v hv)),
  Spec.MlKem1024.keyGenApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.keyGen1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.keyGen x2.sha3 (fixedHash v.callee) v.callee Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.keyGenP1024_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.keyGen1024Ok_tables 160) (Proof.MlKem.AArch64.Scrub.keyGen1024Side x2 hx2 v hv)),
  Spec.MlKem1024.encapsApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encaps1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.encapsP1024_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.encaps1024Ok_tables 160) (Proof.MlKem.AArch64.Scrub.encaps1024Side x2 hx2 v hv)),
  Spec.MlKem1024.encapsHApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.encapsH1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.encapsH x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.encapsHP1024_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.encapsH1024Ok_tables 160) (Proof.MlKem.AArch64.Scrub.encapsH1024Side x2 hx2 v hv)),
  Spec.MlKem1024.decapsApi.artifact AArch64.target (AArch64.ScrubAll.scrubAllOf {
    suffix := qualifiedName "" (parts x2 v)
    vendor := v.vendor
    code := Impl.MlKem.AArch64.Wipe.decaps1024 (qualifiedName "" (parts x2 v))
      (Impl.MlKem.AArch64.Kem16P.decaps x2.sha3 (fixedHash v.callee) (prfW v.callee) Impl.MlKem1024.AArch64.lay1024)
    verified := Proof.MlKem.AArch64.Wipe.decapsP1024_verified (sha3 := x2.sha3) v _ } Proof.MlKem.AArch64.Scrub.clear
    (Proof.MlKem.AArch64.Scrub.decaps1024Ok_tables 160) (Proof.MlKem.AArch64.Scrub.decaps1024Side x2 hx2 v hv))]

/-- The functions over the two-state permutation `x2` and the single-state
one `v`, for every pair but the baseline `x2` with the SHA-3 `v` (`paired`). -/
def artifacts (x2 : Proof.Sha3.AArch64.X2Permutation)
    (hx2 : x2 ∈ VG.Proof.Variants.KeccakX2.AArch64.variants) (v : Proof.Sha3.AArch64.Permutation)
    (hv : v ∈ VG.Proof.Variants.Keccak.AArch64.variants) : List Artifact :=
  if paired x2 v then pairedArtifacts x2 hx2 v hv else []

end VG.Artifacts.MlKem.AArch64.KeccakX2Keccak

namespace VG.Artifacts.MlKem.AArch64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.KeccakX2.AArch64.variants.attach.flatMap fun v =>
    VG.Proof.Variants.Keccak.AArch64.variants.attach.flatMap fun v2 => KeccakX2Keccak.artifacts v.1 v.2 v2.1 v2.2) ++
  [
    Spec.MlKem1024.checkEkApi.artifact AArch64.target {
      code := Proof.MlKem.AArch64.Residue.checkEk1024Cleared
      verified := .scrubbed ⟨Proof.MlKem.AArch64.Residue.checkEk1024Cleared_verified,
        Proof.MlKem.AArch64.Residue.checkEk1024Cleared_noResidue _⟩ }]

end VG.Artifacts.MlKem.AArch64
