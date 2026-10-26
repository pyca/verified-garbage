module

public import VerifiedGarbage.Proof.Bignum.X86.CrtInputs
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs

/-! # Private-call resources depend only on the eighteen cdecl arguments -/

@[expose] public section
namespace VG.Proof.Bignum.X86.Crt
open VG VG.X86

theorem Inputs.argsEq {base : Addr} {bytes len : Nat} {args other : Nat → BitVec 32} {s : State}
    (H : Inputs base bytes len args s) (eq : ∀ i < 18, args i = other i) :
    Inputs base bytes len other s := by
  have H0 := eq 0 (by decide)
  have H1 := eq 1 (by decide)
  have H3 := eq 3 (by decide)
  have H5 := eq 5 (by decide)
  have H7 := eq 7 (by decide)
  have H9 := eq 9 (by decide)
  have H11 := eq 11 (by decide)
  have H13 := eq 13 (by decide)
  have H15 := eq 15 (by decide)
  refine ⟨H.scratch, H.lower, H.upper, H.space, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, H.room, H.top⟩
  · intro i hi; rw [← eq i hi]; exact H.stack i hi
  · rw [← H1]; exact H.outLen
  · rw [← H3]; exact H.nLen
  · rw [← H5]; exact H.inLen
  · rw [← H7]; exact H.pShort
  · rw [← H9]; exact H.qShort
  · rw [← H11, ← H7]; exact H.dpLen
  · rw [← H13, ← H9]; exact H.dqLen
  · rw [← H15, ← H7]; exact H.qiLen
  · rw [← H0]; exact H.outFit
  · rw [← H0]; exact H.outWrite
  · rw [← H0]; exact H.outApart
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq (i + 1) bound]; exact H.positive i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq (i + 1) bound]; exact H.bounded i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega), ← eq (i + 1) bound]; exact H.fits i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega), ← eq (i + 1) bound]; exact H.readable i hi
  · intro i hi
    have bound : i + 1 < 18 := by
      simp only [componentArguments, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [← eq i (by omega), ← eq (i + 1) bound]; exact H.apart i hi

end VG.Proof.Bignum.X86.Crt
