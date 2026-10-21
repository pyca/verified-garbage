module

import VerifiedGarbage.Spec.Ffdh.ScreenedGeneration
import VerifiedGarbage.Proof.Ffdh.GenerationTape
import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ScreenedStream
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Spec.Ffdh.ScreenedCandidate

/-! The screened candidate and each witness batch consume only a bounded entropy prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.ScreenedGeneration
open VG VG.Spec.Ffdh VG.Spec.RsaKeyGen VG.Proof.Ffdh.ParameterCandidate

private theorem suffix_trans {r middle rest : Rand}
    (first : ∃ used ≤ r.length, middle = r.drop used)
    (second : ∃ used ≤ middle.length, rest = middle.drop used) :
    ∃ used ≤ r.length, rest = r.drop used := by
  obtain ⟨a, boundA, mid⟩ := first
  obtain ⟨b, boundB, last⟩ := second
  refine ⟨a + b, ?_, ?_⟩
  · rw [mid, List.length_drop] at boundB
    omega
  · rw [last, mid, List.drop_drop]

private theorem width_pos {w : Nat} (shape : primeShape w = true) : 0 < witnessOctets w := by
  have large : 2 < w := by
    simp only [primeShape, Bool.and_eq_true, decide_eq_true_eq] at shape
    exact shape.1.1
  have nonzero : w - 1 ≠ 0 := by omega
  simp only [witnessOctets, bitLength, nonzero, ite_false]
  omega

private theorem checks_suffix {p q : Nat} {r rest : Rand} {pass : Bool}
    (shapeP : primeShape p = true) (shapeQ : primeShape q = true)
    (run : screenedParameterWitnesses p q r = some (pass, rest)) :
    ∃ used ≤ r.length, rest = r.drop used := by
  rw [← screenedChecks_eq shapeP shapeQ] at run
  unfold screenedChecks at run
  simp only [bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨first, afterP⟩, firstRun, run⟩ := run
  have prefixP := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeP) _ _ _ _ firstRun
  dsimp only at run
  split at run
  · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
    exact run.2 ▸ prefixP
  · simp only [Option.bind_eq_some_iff] at run
    obtain ⟨⟨qpass, afterQ⟩, qRun, run⟩ := run
    have prefixQ := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeQ) _ _ _ _ qRun
    dsimp only at run
    split at run
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact run.2 ▸ suffix_trans prefixP prefixQ
    · have prefixRest := VG.Proof.Ffdh.Generation.checkWitnesses_suffix (width_pos shapeP) _ _ _ _ run
      exact suffix_trans prefixP (suffix_trans prefixQ prefixRest)

theorem candidate_suffix {bits generator : Nat} {r rest : Rand} {p : Option Nat}
    (run : screenedParameterCandidate bits generator r = some (p, rest)) :
    ∃ used ≤ r.length, rest = r.drop used := by
  unfold screenedParameterCandidate at run
  by_cases enough : (bits + 7) / 8 ≤ r.length
  · rw [draw_of_le enough] at run
    simp only [bind, Option.bind_some] at run
    split at run
    · simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact ⟨(bits + 7) / 8, enough, run.2.symm⟩
    · rename_i valid
      have shapes := Bool.eq_false_iff.mpr valid
      simp only [Bool.not_eq_false', Bool.and_eq_true] at shapes
      simp only [Option.bind_eq_some_iff] at run
      obtain ⟨⟨pass, tail⟩, witnesses, run⟩ := run
      have after := checks_suffix shapes.1.2 shapes.2 witnesses
      simp only [pure, Option.some.injEq, Prod.mk.injEq] at run
      exact run.2 ▸ suffix_trans ⟨(bits + 7) / 8, enough, rfl⟩ after
  · rw [draw_of_short (by omega : r.length < (bits + 7) / 8)] at run
    cases run

end VG.Proof.Ffdh.ScreenedGeneration
