module

public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.AttemptVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Framework.Registration
public import VerifiedGarbage.TCB.X86_64.Print
public import VerifiedGarbage.Proof.Variants.MillerRabin.X86_64

/-! # Emit FFDH key generation from the context for every shared arithmetic backend -/

@[expose] public section

namespace VG.Artifacts.CachedFfdh.X86_64

def artifactsFor (v : Proof.MillerRabin.X86_64.RoundImpl) : List Artifact :=
  if v.roundOnly then [] else [
  Spec.Ffdh.generationPrecomputeApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.Cached.precomputeCode v
    verified := Proof.Ffdh.X86_64.Cached.precomputeCode_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.precomputeCode_sp v
    features := v.arithFeatures },
  Spec.Ffdh.cachedGenerateKeyApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 8
    code := Proof.Ffdh.X86_64.Cached.attemptCode v
    verified := Proof.Ffdh.X86_64.Cached.attemptCode_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.attemptCode_sp v
    features := v.arithFeatures },
  Spec.Ffdh.cachedKeySearchApi.artifact X86_64.target {
    suffix := v.suffix
    stack := 72
    code := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode v
    verified := Proof.Ffdh.X86_64.Cached.SearchProof.key_verified v
    spSafe := Proof.Ffdh.X86_64.Cached.SearchProof.keyCode_sp v
    features := v.arithFeatures }]

def artifacts : List Artifact :=
  VG.Proof.Variants.MillerRabin.X86_64.variants.flatMap fun v => artifactsFor v

end VG.Artifacts.CachedFfdh.X86_64
