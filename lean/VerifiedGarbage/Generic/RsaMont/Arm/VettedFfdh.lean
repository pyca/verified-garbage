module

public import VerifiedGarbage.Proof.Ffdh.Arm.VettedKeyInstances
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! Vetted sampling inherits every callable RSA Montgomery backend. -/

@[expose] public section
namespace VG.Generic.RsaMont.Arm.VettedFfdh
open VG

def artifacts (v : Proof.Bignum.Arm.MontBackend) : List Artifact :=
  [Spec.Ffdh.vettedGenerateKeyApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := 176
    consts := Impl.Ffdh.Arm.VettedGroups.tableConsts
    code := Proof.Ffdh.Arm.VettedKeyGenerate.code v
    verified := Proof.Ffdh.Arm.VettedKeyGenerate.verified v
    notes := ["ARMv7: one shared table recognizes exact vetted MODP/FFDHE domains. \
      The reviewed public cap selects both entropy masking and a fixed exponentiation \
      width, including secret leading zeros. Other domains retain full-width sampling. \
      Product and specialized square operations call the shared RSA Montgomery helper."] },
  Spec.Ffdh.vettedKeySearchApi.artifact VG.Arm.target {
    suffix := v.suffix
    features := v.features
    stack := Proof.Ffdh.Arm.KeySearch.stackUse
    consts := Impl.Ffdh.Arm.VettedGroups.tableConsts
    code := Impl.Ffdh.Arm.KeySearch.code
      (.call (Proof.Ffdh.Arm.VettedKeyGenerate.backend v).keyName
        (Proof.Ffdh.Arm.VettedKeyGenerate.backend v).generateKey)
    verified := Proof.Ffdh.Arm.KeySearch.verified (Proof.Ffdh.Arm.VettedKeyGenerate.backend v)
    notes := ["ARMv7: the shared native retry controller calls the vetted attempt, \
      retaining both rejection budgets, full-size entropy requests, and refill behavior. \
      Both entry points and every Montgomery backend share the same vetted-group table."] }]

end VG.Generic.RsaMont.Arm.VettedFfdh
