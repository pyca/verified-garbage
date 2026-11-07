module

public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Emit FFDH domain operations for every shared arithmetic backend and exponentiation -/

@[expose] public section

namespace VG.Generic.MillerRabin.FfdhExp.X86_64.Ffdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) (e : Proof.Ffdh.X86_64.ExpImpl) : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPublic.publicCode v e
    verified := Proof.Ffdh.X86_64.CheckPublic.publicCode_verified v e
    spSafe := Proof.Ffdh.X86_64.CheckPublic.publicCode_sp v e
    features := v.arithFeatures ++ e.features },
  Spec.Ffdh.exchangeApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.Exchange.exchangeCode v e
    verified := Proof.Ffdh.X86_64.Exchange.exchangeCode_verified v e
    spSafe := Proof.Ffdh.X86_64.Exchange.exchangeCode_sp v e
    features := v.arithFeatures ++ e.features },
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPrivate.privateCode v e
    verified := Proof.Ffdh.X86_64.CheckPrivate.privateCode_verified v e
    spSafe := Proof.Ffdh.X86_64.CheckPrivate.privateCode_sp v e
    features := v.arithFeatures ++ e.features },
  Spec.Ffdh.derivePublicApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.DerivePublic.deriveCode v e
    verified := Proof.Ffdh.X86_64.DerivePublic.deriveCode_verified v e
    spSafe := Proof.Ffdh.X86_64.DerivePublic.deriveCode_sp v e
    features := v.arithFeatures ++ e.features },
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    suffix := Emit.qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.VettedValidation.emittedCode v e
    verified := Proof.Ffdh.X86_64.VettedValidation.verified v e
    spSafe := Proof.Ffdh.X86_64.VettedValidation.sp_safe v e
    features := v.arithFeatures ++ e.features }]

end VG.Generic.MillerRabin.FfdhExp.X86_64.Ffdh
