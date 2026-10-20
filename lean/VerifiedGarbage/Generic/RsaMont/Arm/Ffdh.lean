module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeyInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Emit key generation and its retry controller for every Montgomery backend. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.Ffdh
open VG

def artifacts (v : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.generateKeyApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 176
    code := (Proof.Ffdh.Arm.KeyGenerate.backend v).generateKey
    verified := (Proof.Ffdh.Arm.KeyGenerate.backend v).generateKey_verified
    notes := ["ARMv7: generator two uses a fixed square/double/select schedule; other \
      generators use three-bit windows. Montgomery setup, multiplication and specialized \
      squaring call one shared RSA arithmetic helper per backend. Sampling retains \
      the public bound's significant byte width, including secret leading zeros. \
      A generated power's subgroup membership follows from the checked generator."] },
  Spec.Ffdh.keySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := Proof.Ffdh.Arm.KeySearch.stackUse
    code := Impl.Ffdh.Arm.KeySearch.code
      (.call (Proof.Ffdh.Arm.KeyGenerate.backend v).keyName
        (Proof.Ffdh.Arm.KeyGenerate.backend v).generateKey)
    verified := Proof.Ffdh.Arm.KeySearch.verified (Proof.Ffdh.Arm.KeyGenerate.backend v)
    notes := ["ARMv7: native rejection sampling owns both bounded retry counters, consumes \
      the entropy tape, clears incomplete outputs, and requests entropy refills. \
      The callable key-generation attempt inherits every shared Montgomery variant."] }]

end VG.Generic.RsaMont.Arm.Ffdh
