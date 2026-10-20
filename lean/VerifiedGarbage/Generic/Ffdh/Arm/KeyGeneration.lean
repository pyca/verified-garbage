module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Emit native rejection/refill controllers for every FFDH arithmetic backend. -/

@[expose] public section
namespace VG.Generic.Ffdh.Arm.KeyGeneration
open VG

def artifacts (v : Proof.Ffdh.Arm.Backend) : List Artifact :=
  [Spec.Ffdh.keySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := Proof.Ffdh.Arm.KeySearch.stackUse
    code := Impl.Ffdh.Arm.KeySearch.code (.call v.keyName v.generateKey)
    verified := Proof.Ffdh.Arm.KeySearch.verified v
    notes := ["ARMv7: native rejection sampling owns both bounded retry counters, consumes \
      the entropy tape, clears incomplete outputs, and requests entropy refills. The \
      chosen arithmetic backend propagates through the callable key-generation attempt. \
      Four packed-u64 policy words retain exact values across ARM's native 32-bit stores."] }]

end VG.Generic.Ffdh.Arm.KeyGeneration
