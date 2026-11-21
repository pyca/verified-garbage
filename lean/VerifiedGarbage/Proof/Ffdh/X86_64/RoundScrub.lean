module

public import VerifiedGarbage.Impl.Ffdh.X86_64.Fn
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.PrecomputeVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Cached.SearchProof.Verified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Generation.SearchVerified
public import VerifiedGarbage.Proof.Ffdh.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubFillG
import VerifiedGarbage.Proof.Framework.Lit

/-!
# FFDH's functions over the Miller–Rabin round on x86-64, without secret residue

`vg_ffdh_generate_key_precompute`, `vg_ffdh_generate_key_search_cached` and
`vg_ffdh_generate_parameters` as emitted (`Impl.Ffdh.X86_64.Fn`), over any
implementation of the Miller–Rabin round and its arithmetic (`RoundImpl`),
each with its whole stack wiped by its cleanup at the implementation's
level. Each one's code is its code over a stub of the multiplication (and
of the round), with the implementation's where it runs them (`FillG`,
`fill_gen`): the kernel evaluates what the cleanup needs of the stub once,
and the implementation what it needs of its own code where it is defined
(`RoundImpl.mmSide`, `RoundImpl.montSide`, `RoundImpl.side`).
-/

-- separate module: the kernel's evaluation of the cleanup's side conditions, which a registration file may not hold

@[expose] public section

namespace VG.Proof.Ffdh.X86_64.RoundScrub

open VG.X86_64 VG.X86_64.Scrub VG.Impl.Scrub.X86_64
open VG.Proof.MillerRabin.X86_64 (RoundImpl)

/-- A stub of the Montgomery multiplication. -/
abbrev stubMM : Nat → Nat → Nat → Prog isa := fun _ _ _ => .call "mm" (.block [])

/-- The stack the multiplication (called) needs. -/
def mmStack : String → Nat := fun _ => 8

theorem precompute_stub :
    stubSideG (Cached.codeWith stubMM) VecLevel.sse.level mmStack 8 [] = true := by lit_decide

/-- `Spec.Ffdh.generationPrecomputeApi`'s function as emitted over `v` meets
its contract in constant time and returns without secret residue. -/
theorem precompute_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.generationPrecompute v.level v.mm)
      (Spec.Ffdh.generationPrecomputeApi.contract (X86_64.abi.withConsts Impl.Ffdh.X86_64.VettedValidation.tableConsts) 8)
      32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.generationPrecomputeApi)
    { code := Cached.precomputeCode v
      verified := Cached.precomputeCode_verified v
      spSafe := Cached.precomputeCode_sp v } _
    (Proof.Ffdh.X86_64.Scrub.generationPrecomputeOut 8 Impl.Ffdh.X86_64.VettedValidation.tableConsts)
    (by have hm := v.mmSide; unfold Cached.precomputeCode Cached.codeWith; fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := precompute_stub)

theorem precompute_spSafe (v : RoundImpl) :
    (Impl.Ffdh.X86_64.Fn.generationPrecompute v.level v.mm).all (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Cached.precomputeCode_sp v)

theorem key_stub :
    stubSideG (Impl.Ffdh.X86_64.Cached.Search.code (.call "a" (Cached.attemptWith stubMM))) VecLevel.sse.level
      mmStack 72 [] = true := by lit_decide

/-- `Spec.Ffdh.cachedKeySearchApi`'s function as emitted over `v` meets its
contract in constant time and returns without secret residue. -/
theorem key_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target
      (Impl.Ffdh.X86_64.Fn.cachedKeySearch v.level ("vg_ffdh_generate_key_cached" ++ v.suffix) v.mm)
      (Spec.Ffdh.cachedKeySearchApi.contract X86_64.abi 72) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.cachedKeySearchApi)
    { code := Cached.SearchProof.keyCode v
      verified := Cached.SearchProof.key_verified v
      spSafe := Cached.SearchProof.keyCode_sp v } _
    (Proof.Ffdh.X86_64.Scrub.cachedKeySearchOut _)
    (by
      have hm := v.mmSide
      unfold Cached.SearchProof.keyCode Cached.SearchProof.attemptCall Cached.attemptCode Cached.attemptWith
      fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := key_stub)

theorem key_spSafe (v : RoundImpl) :
    (Impl.Ffdh.X86_64.Fn.cachedKeySearch v.level ("vg_ffdh_generate_key_cached" ++ v.suffix) v.mm).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Cached.SearchProof.keyCode_sp v)

/-- The stack the round (called) and the multiplication (inline) need. -/
def searchStack : String → Nat := fun s => if s = "r" then 128 else 0

theorem search_stub :
    stubSideG (Impl.Ffdh.X86_64.Generation.Search.code (Impl.Ffdh.X86_64.ParameterCandidate.code stubMM
      (Impl.Bignum.X86_64.R2Words.choice stubMM) (Impl.MillerRabin.X86_64.Caller.call "r" (.block []))))
      VecLevel.sse.level searchStack 160 [] = true := by lit_decide

/-- `Spec.Ffdh.sievedParameterSearchApi`'s function as emitted over `v`
meets its contract in constant time and returns without secret residue. -/
theorem search_scrubbed (v : RoundImpl) :
    VerifiedScrubbed target (Impl.Ffdh.X86_64.Fn.sievedParameterSearch v.level v.mont.mm v.name v.code)
      (Spec.Ffdh.sievedParameterSearchApi.contract X86_64.abi 160) 32 :=
  verifiedScrubbedAllFillG (api := Spec.Ffdh.sievedParameterSearchApi)
    { code := Generation.searchCode v
      verified := Generation.search_verified v
      spSafe := Generation.searchCode_sp v } _
    (Proof.Ffdh.X86_64.Scrub.sievedParameterSearchOut _)
    (by
      have hm := v.montSide
      have hr := v.side
      unfold Generation.searchCode ParameterCandidate.candidateCode
      fill_gen)
    (Nat.zero_le _) (Nat.le_refl _) (ha := search_stub)

theorem search_spSafe (v : RoundImpl) :
    (Impl.Ffdh.X86_64.Fn.sievedParameterSearch v.level v.mont.mm v.name v.code).all
      (fun i => !isa.writesSp i) = true :=
  scrubKs_spSafe (Generation.searchCode_sp v)

end VG.Proof.Ffdh.X86_64.RoundScrub
