module

public import VerifiedGarbage.Impl.Ffdh.PPC64LE.Cached
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Contract
public import VerifiedGarbage.Spec.Ffdh.CachedKeyGenerationContract
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptCorrect
public import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.AttemptVerified
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Correct
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.CT
import VerifiedGarbage.Proof.Ffdh.PPC64LE.Cached.SearchProof.Implies

/-! # The verified cached key search (PPC64LE)

For any cached attempt that uses no stack of its own (`key_verified_of`),
and for `vg_ffdh_generate_key_cached` (`cachedAttempt`, `search_verified`).
-/

@[expose] public section

namespace VG.Proof.Ffdh.PPC64LE.Cached.SearchProof

open VG VG.PPC64LE

theorem key_verified_of (a : Attempt) :
    Verified target (Impl.Ffdh.PPC64LE.Cached.Search.code a.call)
      (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
  Verified.of_correct (key_correct a) (key_constantTime a) key_implies

/-- `vg_ffdh_generate_key_cached`, which has no frames. -/
def cachedAttempt : Attempt where
  name := Spec.Ffdh.cachedGenerateKeyApi.name
  code := Impl.Ffdh.PPC64LE.Cached.Generate.code
  stack := by decide +kernel
  correct := Cached.cg_correct
  ct := Cached.cg_ct

/-- The cached key search calling it. -/
abbrev keyCode : Prog isa := Impl.Ffdh.PPC64LE.Cached.Search.code cachedAttempt.call

theorem search_verified : Verified target keyCode (Spec.Ffdh.cachedKeySearchContract abi stackUse) :=
  key_verified_of cachedAttempt

end VG.Proof.Ffdh.PPC64LE.Cached.SearchProof
