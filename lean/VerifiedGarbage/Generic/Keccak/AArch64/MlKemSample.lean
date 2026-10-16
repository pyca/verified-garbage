module

public import VerifiedGarbage.Proof.MlKem.AArch64.Sample
import Mathlib.Tactic.Conv
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Proof.Framework.Registration

@[expose] public section

namespace VG.Generic.Keccak.AArch64.MlKemSample

def artifacts (v : Proof.Sha3.AArch64.Permutation) : List Artifact := [
  Spec.MlKem.sampleNTTApi.artifact AArch64.target {
    suffix := v.callee.suffix
    features := v.features
    code := Impl.MlKem.AArch64.sampleNTTWith v.callee
    stack := 16
    verified := Proof.MlKem.AArch64.Sample.sample_verifiedWith v }]

end VG.Generic.Keccak.AArch64.MlKemSample
