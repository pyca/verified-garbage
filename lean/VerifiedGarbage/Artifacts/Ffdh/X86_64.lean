module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Verified
public import VerifiedGarbage.Proof.Ffdh.X86_64.VettedValidation.Safety
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPrivate.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.CheckPublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.DerivePublic.Backend
public import VerifiedGarbage.Proof.Ffdh.X86_64.Exchange.Backend
public import VerifiedGarbage.TCB.Emit
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64
public import VerifiedGarbage.Proof.Variants.FfdhExp.X86_64
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchVerified

/-! # Emit FFDH domain operations for every shared arithmetic backend and exponentiation -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact target {
    code := Impl.Ffdh.X86_64.Generation.init
    verified := Proof.Ffdh.X86_64.Generation.init_verified },
  Spec.Ffdh.keyInitApi.artifact target {
    code := Impl.Ffdh.X86_64.KeyGeneration.init
    verified := Proof.Ffdh.X86_64.KeyGeneration.init_verified }]
end VG.Artifacts.Ffdh.X86_64

-- Emit FFDH domain operations for every shared arithmetic backend and exponentiation
namespace VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) (e : Proof.Ffdh.X86_64.ExpImpl) : List Artifact :=
  if v.roundOnly then [] else [
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

end VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

-- Emit FFDH parameter search for every shared arithmetic backend
namespace VG.Artifacts.Ffdh.X86_64.MillerRabin

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.Ffdh.sievedParameterSearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 160
    code := Proof.Ffdh.X86_64.Generation.searchCode v
    verified := Proof.Ffdh.X86_64.Generation.search_verified v
    spSafe := Proof.Ffdh.X86_64.Generation.searchCode_sp v
    features := v.features }]

end VG.Artifacts.Ffdh.X86_64.MillerRabin

namespace VG.Artifacts.Ffdh.X86_64

def artifacts : List Artifact :=
  direct ++
  (VG.Proof.Variants.FfdhExp.X86_64.variants.flatMap fun v2 =>
    VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun v => MillerRabinFfdhExp.artifacts v v2) ++
  (VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun v => MillerRabin.artifacts v)

end VG.Artifacts.Ffdh.X86_64
