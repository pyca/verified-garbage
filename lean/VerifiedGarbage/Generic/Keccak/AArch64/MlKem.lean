module

public import VerifiedGarbage.Proof.MlKem1024.AArch64.KeyGen
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Encaps
public import VerifiedGarbage.Proof.MlKem1024.AArch64.Decaps
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.KeyGenFinal
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.EncapsVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.FixedHash.DecapsVerified
public import VerifiedGarbage.Proof.MlKem.AArch64.Hybrid.Final
public import VerifiedGarbage.Proof.Framework.Registration

/-! `keygen`, `encaps` and `decaps` of ML-KEM-768 and ML-KEM-1024, for each
Keccak implementation: with the SHA-3 extension, the paired sampling and fused
arithmetic of `optimizedArtifacts`; otherwise (the scalar baseline) the code of
`legacyArtifacts`, over the sponge functions of the implementation. -/

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlKem

/-- One Keccak state at a time, over the sponge functions of `v`. -/
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

def hybridNote : String :=
  "Computes `H(ek)` in the third state of `vg_keccak_f1600_x3_sha3`, one block of `ek` per main \
  squeeze of the matrix's first pairs, while the vector unit runs their SHAKE128 states."

/-- Paired sampling and fused arithmetic for the hardware SHA3 backend: its
instances of `keygen`, `encaps` and `decaps`, which call the permutations
(`vg_keccak_f1600_sha3`, `vg_keccak_f1600_x2_sha3` and, in `encaps`,
`vg_keccak_f1600_x3_sha3`) rather than the sponge functions. -/
def optimizedArtifacts : List Artifact := [
  Spec.MlKem.keyGenApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem.AArch64.lay768
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen768_final },
  Spec.MlKem.encapsApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    notes := [hybridNote]
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Hybrid.encaps Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    stack := 128
    verified := Proof.MlKem.AArch64.Hybrid.encapsH768_verified },
  Spec.MlKem.decapsApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem.AArch64.lay768
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps768_verified },
  Spec.MlKem1024.keyGenApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashCallers.keyGenUsing Proof.MlKem.AArch64.FixedHash.fixedHash Impl.MlKem1024.AArch64.lay1024
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.keyGen1024_final },
  Spec.MlKem1024.encapsApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    notes := [hybridNote]
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.Hybrid.encaps Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    stack := 128
    verified := Proof.MlKem.AArch64.Hybrid.encapsH1024_verified },
  Spec.MlKem1024.decapsApi.artifact AArch64.target {
    suffix := "_sha3"
    features := Proof.Sha3.AArch64.Sha3.backend.features
    consts := Proof.MlKem.AArch64.Optimized.constants
    code := Impl.MlKem.AArch64.FixedHashDecaps.decapsUsing Proof.MlKem.AArch64.FixedHash.fixedHash Proof.MlKem.AArch64.FixedHash.prf Impl.MlKem1024.AArch64.lay1024
    stack := 16
    verified := Proof.MlKem.AArch64.FixedHash.decaps1024_verified }]

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if v.callee.pairedSha3 then optimizedArtifacts else legacyArtifacts v

end VG.Generic.Keccak.AArch64.MlKem
