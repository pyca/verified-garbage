import VerifiedGarbage.Proof.Framework.AArch64.Inline
import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved

/-!
# The ABI of the curve functions on AArch64

The functions built on ECDSA's code save and restore `x19` and `x20`, and
no instruction of theirs writes the other callee-saved registers
(`untouched`), which one check of every instruction shows
(`keeps_untouched`, by `lit_decide` on the code's literal); so with `x19`
and `x20` restored they preserve what the ABI asks (`abiPreserved_of`).
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64

/-- The callee-saved registers but `x19` and `x20`. -/
abbrev untouched : List Reg := [.x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x30]

/-- Whether no instruction writes a register of `untouched`. -/
abbrev KeepsUntouched (c : Prog isa) : Prop :=
  c.allInstrs (fun i => (dstOf i).all fun r => !untouched.contains r) = true

theorem keeps_untouched {c : Prog isa} (h : KeepsUntouched c) :
    ∀ i ∈ instrs c, ∀ r ∈ untouched, dstOf i ≠ some r := by
  rw [KeepsUntouched, Code.allInstrs_eq, List.all_eq_true] at h
  intro i hi r hr he
  have := h i hi
  rw [he] at this
  simp only [Option.all_some, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at this
  exact this hr

/-- A run that restores `x19` and `x20` and writes no other callee-saved
register, nor a SIMD register, and calls nothing, preserves what the ABI asks. -/
theorem abiPreserved_of {c : Prog isa} {s s' : State} {t : List Leak} (he : Exec isa c s t s')
    (hn : c.noCalls = true) (hu : KeepsUntouched c) (hv : c.allInstrs keepsV = true)
    (hsv : ∀ r ∈ [Reg.x19, .x20], s'.gpr r = s.gpr r) : abiPreserved s s' := by
  refine ⟨fun r hr => ?_, Exec.sp he, Exec.preservedV he hv⟩
  by_cases h : r ∈ untouched
  · exact Exec.gpr (fun i hi => keeps_untouched hu i hi r h) he (.inl hn)
  · refine hsv r ?_
    revert h
    revert r
    decide

end VG.Proof.Ecdsa.AArch64
