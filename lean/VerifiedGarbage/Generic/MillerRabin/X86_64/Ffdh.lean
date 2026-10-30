module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.GenerateKey.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Verified
public import VerifiedGarbage.Proof.Framework.Registration

/-! # Emit FFDH domain operations for every shared arithmetic backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.Ffdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPublic.publicCode v
    verified := Proof.Ffdh.X86_64.CheckPublic.publicCode_verified v
    spSafe := Proof.Ffdh.X86_64.CheckPublic.publicCode_sp v
    features := v.features },
  Spec.Ffdh.exchangeApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.Exchange.exchangeCode v
    verified := Proof.Ffdh.X86_64.Exchange.exchangeCode_verified v
    spSafe := Proof.Ffdh.X86_64.Exchange.exchangeCode_sp v
    features := v.features },
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPrivate.privateCode v
    verified := Proof.Ffdh.X86_64.CheckPrivate.privateCode_verified v
    spSafe := Proof.Ffdh.X86_64.CheckPrivate.privateCode_sp v
    features := v.features },
  Spec.Ffdh.derivePublicApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.DerivePublic.deriveCode v
    verified := Proof.Ffdh.X86_64.DerivePublic.deriveCode_verified v
    spSafe := Proof.Ffdh.X86_64.DerivePublic.deriveCode_sp v
    features := v.features },
  Spec.Ffdh.generateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.GenerateKey.generateCode v
    verified := Proof.Ffdh.X86_64.GenerateKey.generateCode_verified v
    spSafe := Proof.Ffdh.X86_64.GenerateKey.generateCode_sp v
    features := v.features },
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    consts := Impl.Ffdh.X86_64.VettedValidation.tableConsts
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.VettedValidation.emittedCode v
    verified := Proof.Ffdh.X86_64.VettedValidation.verified v
    spSafe := Proof.Ffdh.X86_64.VettedValidation.sp_safe v
    features := v.features },
  Spec.Ffdh.parameterSearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 160
    code := Proof.Ffdh.X86_64.Generation.searchCode v
    verified := Proof.Ffdh.X86_64.Generation.search_verified v
    spSafe := Proof.Ffdh.X86_64.Generation.searchCode_sp v
    features := v.features },
  Spec.Ffdh.keySearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 56
    code := Proof.Ffdh.X86_64.KeyGeneration.keyCode v
    verified := Proof.Ffdh.X86_64.KeyGeneration.key_verified v
    spSafe := Proof.Ffdh.X86_64.KeyGeneration.keyCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.Ffdh
