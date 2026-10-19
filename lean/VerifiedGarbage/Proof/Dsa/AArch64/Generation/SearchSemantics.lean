module

public import VerifiedGarbage.Proof.Dsa.AArch64.Generation.SearchBody
public import VerifiedGarbage.Proof.Dsa.Generation.Search
import VerifiedGarbage.Proof.Framework.Omega

/-! # Match each native body result to the reviewed p-search recursion -/

@[expose] public section
namespace VG.Proof.Dsa.AArch64.Generation
open VG VG.AArch64

def SearchPlan.remaining (p : SearchPlan) (counter used : Nat) : Option (Option Nat × List Byte) :=
  VG.Proof.Dsa.Generation.primeSearch (8 * p.attempt.construct.len) (8 * p.attempt.construct.hash.len)
    (Spec.Rsa.os2ip p.attempt.construct.qb) p.attempt.construct.hash.seed counter (p.attempt.rand.drop used)

theorem SearchPlan.stepCursor {p : SearchPlan} {counter used : Nat} {b : Bool} {rest : List Byte}
    (h : p.stepResult counter used = some (b, rest)) :
    p.attempt.rand.drop (p.attempt.rand.length - rest.length) = rest := by
  unfold SearchPlan.stepResult at h
  split at h
  · cases h
    apply VG.Proof.Dsa.Generation.suffix_drop_length
    exact List.drop_suffix _ _
  · exact VG.Proof.Dsa.Generation.probablePrime_cursor h

theorem SearchPlan.remaining_step {p : SearchPlan} {counter used : Nat}
    (hc : counter < 32 * p.attempt.construct.len) :
    p.remaining counter used =
      match p.stepResult counter used with
      | none => none
      | some (true, rest) => some (some (p.candidate counter), rest)
      | some (false, rest) => p.remaining (counter + 1) (p.attempt.rand.length - rest.length) := by
  have hc' : counter < 4 * (8 * p.attempt.construct.len) := by omega
  unfold SearchPlan.remaining
  rw [VG.Proof.Dsa.Generation.primeSearch_step _ _ hc']
  rw [← p.attempt.construct.hashCount]
  change (if p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1) then _ else _) = _
  by_cases hs : p.candidate counter < 2 ^ (8 * p.attempt.construct.len - 1)
  · simp only [hs, ite_true, SearchPlan.stepResult]
    rw [VG.Proof.Dsa.Generation.suffix_drop_length (List.drop_suffix used p.attempt.rand)]
  · simp only [hs, ite_false, SearchPlan.stepResult]
    rcases hp : Spec.Dsa.probablePrime (p.candidate counter) (p.attempt.rand.drop used) with _ | ⟨b, rest⟩
    · simp only [SearchPlan.candidate] at hp
      rw [hp]
    · have hp' := hp
      simp only [SearchPlan.candidate] at hp'
      rw [hp']
      cases b
      · simp only [Bool.false_eq_true, ite_false]
        rw [VG.Proof.Dsa.Generation.probablePrime_cursor hp]
      · rfl

theorem SearchPlan.remaining_done (p : SearchPlan) (used : Nat) :
    p.remaining (32 * p.attempt.construct.len) used = some (none, p.attempt.rand.drop used) :=
  VG.Proof.Dsa.Generation.primeSearch_done _ _ (by omega)

end VG.Proof.Dsa.AArch64.Generation
