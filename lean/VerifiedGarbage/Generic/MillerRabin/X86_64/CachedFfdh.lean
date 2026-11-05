module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print

/-! # Emit FFDH key generation from the context for every shared arithmetic backend -/

@[expose] public section

namespace VG.Generic.MillerRabin.X86_64.CachedFfdh

def artifacts (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact := [
  Spec.Ffdh.generationPrecomputeApi.artifact X86_64.target {
    consts := Impl.Ffdh.X86_64.VettedValidation.tableConsts
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.Cached.precomputeCode v
    verified := Proof.Ffdh.X86_64.Cached.precomputeCode_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.precomputeCode_sp v
    features := v.features },
  Spec.Ffdh.cachedGenerateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.Cached.attemptCode v
    verified := Proof.Ffdh.X86_64.Cached.attemptCode_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.attemptCode_sp v
    features := v.features },
  Spec.Ffdh.cachedKeySearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 72
    code := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode v
    verified := Proof.Ffdh.X86_64.Cached.SearchProof.key_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode_sp v
    features := v.features }]

end VG.Generic.MillerRabin.X86_64.CachedFfdh
