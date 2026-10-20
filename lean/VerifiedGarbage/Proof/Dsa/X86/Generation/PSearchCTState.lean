module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateResultCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchTailCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState

/-! # Public p-search counter, witness cursor, and next candidate outcome -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure PSearchPublic (P : PSearchPlan) where
  counter : Nat
  used : Nat
  counterBound : counter < 32 * P.context.geometry.pLen
  usedBound : used ≤ P.context.witnesses.bytes.length

def PSearchPublic.result {P : PSearchPlan} (p : PSearchPublic P) : Nat × Nat :=
  candidatePublicResult P.context (P.value p.counter) p.used

def PSearchPublic.tail {P : PSearchPlan} (p : PSearchPublic P) : SearchTailPublic :=
  ⟨⟨off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control, p.counter,
    P.context.geometry.contributionCount + 1⟩, p.result.1⟩

def PAttemptAnswered (P : PSearchPlan) (p : PSearchPublic P) (s : State) : Prop :=
  (∃ W used, PSearchMemory P W s ∧ W 16 = BitVec.ofNat 32 used ∧ used ≤ P.context.witnesses.bytes.length ∧
    (p.result.1 ≠ 0 → used = p.result.2)) ∧
  SearchTailAt (32 * P.context.geometry.pLen) (P.context.geometry.contributionCount + 1) p.tail s
end VG.Proof.Dsa.X86.Generation
