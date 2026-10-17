module

public import VerifiedGarbage.Proof.MlKem.AArch64.Sample
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlKemSample

/-- `SampleNTT`, which the single-state `keygen`, `encaps` and `decaps` call
(`Generic/KeccakX2/Keccak/AArch64/MlKem.lean`'s `spongeArtifacts`): the
instances with the SHA-3 extension sample with their own paired code, and call
none of these. -/
def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact :=
  if v.callee.pairedSha3 then [] else [
  Spec.MlKem.sampleNTTApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.sampleNTTWith v.callee
    stack := 16
    verified := Proof.MlKem.AArch64.Sample.sample_verifiedWith v }]

end VG.Generic.Keccak.AArch64.MlKemSample
