module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.InitVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.KeyGeneration.Init
public import VerifiedGarbage.Proof.Ffdh.X86_64.InitScrub
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
public import VerifiedGarbage.Proof.Framework.QualifiedName
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Verified

/-! # Finite-field Diffie–Hellman (SP 800-56A) on x86-64 -/

@[expose] public section

namespace VG.Artifacts.Ffdh.X86_64
open VG.X86_64

def direct : List Artifact := [
  Spec.Ffdh.parameterInitApi.artifact target Proof.Ffdh.X86_64.Scrub.parameterInitReg,
  Spec.Ffdh.keyInitApi.artifact target Proof.Ffdh.X86_64.Scrub.keyInitReg]
end VG.Artifacts.Ffdh.X86_64

-- Emit FFDH domain operations for every shared arithmetic backend and exponentiation
namespace VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) (e : Proof.Ffdh.X86_64.ExpImpl) : List Artifact := [
  Spec.Ffdh.checkPublicApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPublic.publicCode v e
    verified := Proof.Ffdh.X86_64.CheckPublic.publicCode_verified v e
    spSafe := Proof.Ffdh.X86_64.CheckPublic.publicCode_sp v e },
  Spec.Ffdh.exchangeApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.Exchange.exchangeCode v e
    verified := Proof.Ffdh.X86_64.Exchange.exchangeCode_verified v e
    spSafe := Proof.Ffdh.X86_64.Exchange.exchangeCode_sp v e },
  Spec.Ffdh.checkPrivateApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.CheckPrivate.privateCode v e
    verified := Proof.Ffdh.X86_64.CheckPrivate.privateCode_verified v e
    spSafe := Proof.Ffdh.X86_64.CheckPrivate.privateCode_sp v e },
  Spec.Ffdh.derivePublicApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.DerivePublic.deriveCode v e
    verified := Proof.Ffdh.X86_64.DerivePublic.deriveCode_verified v e
    spSafe := Proof.Ffdh.X86_64.DerivePublic.deriveCode_sp v e },
  Spec.Ffdh.checkDomainApi.artifact X86_64.target {
    suffix := qualifiedName "" [("mr", v.suffix), ("exp", e.suffix)]
    stack := 8
    code := Proof.Ffdh.X86_64.VettedValidation.emittedCode v e
    verified := Proof.Ffdh.X86_64.VettedValidation.verified v e
    spSafe := Proof.Ffdh.X86_64.VettedValidation.sp_safe v e }]

end VG.Artifacts.Ffdh.X86_64.MillerRabinFfdhExp

namespace VG.Artifacts.Ffdh.X86_64

def artifacts : List Artifact :=
  (VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.generationPrecomputeApi.artifact X86_64.target {
      suffix := v.suffix
      stack := 8
      code := Proof.Ffdh.X86_64.Cached.precomputeCode v
      verified := Proof.Ffdh.X86_64.Cached.precomputeCode_verified v
      spSafe := Proof.Ffdh.X86_64.Cached.precomputeCode_sp v },
    Spec.Ffdh.cachedKeySearchApi.artifact X86_64.target {
      suffix := v.suffix
      stack := 72
      code := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode v
      verified := Proof.Ffdh.X86_64.Cached.SearchProof.key_verified v
      spSafe := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode_sp v }]) ++
  direct ++
  (VG.Proof.Variants.FfdhExp.X86_64.variants.flatMap fun v2 =>
    VG.Proof.Variants.MillerRabin.X86_64.arithVariants.flatMap fun v => MillerRabinFfdhExp.artifacts v v2) ++
  (VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun (v : Proof.MillerRabin.X86_64.RoundImpl) => [
    Spec.Ffdh.sievedParameterSearchApi.artifact X86_64.target {
      suffix := v.suffix
      stack := 160
      code := Proof.Ffdh.X86_64.Generation.searchCode v
      verified := Proof.Ffdh.X86_64.Generation.search_verified v
      spSafe := Proof.Ffdh.X86_64.Generation.searchCode_sp v }])

end VG.Artifacts.Ffdh.X86_64
