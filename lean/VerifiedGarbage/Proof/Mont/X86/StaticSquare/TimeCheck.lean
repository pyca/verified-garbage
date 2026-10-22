module

import VerifiedGarbage.Proof.Framework.X86.TaintErase
import VerifiedGarbage.Proof.Framework.X86.Lit
import VerifiedGarbage.Proof.Framework.LitShare
import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Erase
meta import VerifiedGarbage.Proof.Framework.X86.TaintErase
meta import VerifiedGarbage.Proof.Framework.X86.Lit
meta import VerifiedGarbage.Proof.Framework.LitShare
meta import VerifiedGarbage.Proof.Mont.X86.StaticSquare.Erase
public import VerifiedGarbage.Impl.Mont.X86.StaticSquare
public import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
public import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Impl.Mont.X86.StaticSquare
meta import VerifiedGarbage.Proof.Mont.X86.Rt.ScalarVerified
meta import VerifiedGarbage.Proof.Framework.X86.Taint

/-! # Constant-time checks for the fixed scalar square schedules

The checker receives an explicit certificate, so the kernel validates it
without repeating the invariant search in `hintOf`. -/
@[expose] public section
namespace VG.Proof.Mont.X86.StaticSquare
open VG VG.X86 VG.Proof.Mont.X86.Rt

/-- Transfer the checked certificate back to the original instructions. -/
private theorem check_of_erased {c : Prog isa}
    (h : ∃ hint, (VG.Taint.check taint rtTaint (VG.X86.Code.erase c) hint).isSome = true ∧
      VG.X86.Taint.hintNoBases hint = true) :
    ∃ hint, (VG.Taint.check taint rtTaint c hint).isSome = true := by
  obtain ⟨hint, hc, hn⟩ := h
  refine ⟨hint, ?_⟩
  rw [← VG.X86.Taint.check_erase c rtTaint hint rfl hn]
  exact hc

materialize_shared square32 := Erase.square 32

theorem square32_check : ∃ hint, (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 32)
    hint).isSome=true := by
  apply check_of_erased
  rw [Erase.erase_square]
  exact ⟨_, by
    constructor
    · taint_decide
    · decide +kernel⟩

materialize_shared square48 := Erase.square 48

theorem square48_check : ∃ hint, (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 48)
    hint).isSome=true := by
  apply check_of_erased
  rw [Erase.erase_square]
  exact ⟨_, by
    constructor
    · taint_decide
    · decide +kernel⟩

materialize_shared square64 := Erase.square 64

theorem square64_check : ∃ hint, (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 64)
    hint).isSome=true := by
  apply check_of_erased
  rw [Erase.erase_square]
  exact ⟨_, by
    constructor
    · taint_decide
    · decide +kernel⟩

materialize_shared square96 := Erase.square 96

theorem square96_check : ∃ hint, (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 96)
    hint).isSome=true := by
  apply check_of_erased
  rw [Erase.erase_square]
  exact ⟨_, by
    constructor
    · taint_decide
    · decide +kernel⟩

materialize_shared square128 := Erase.square 128

theorem square128_check : ∃ hint, (VG.Taint.check taint rtTaint
    (Impl.Mont.X86.Rt.StaticSquare.square 128)
    hint).isSome=true := by
  apply check_of_erased
  rw [Erase.erase_square]
  exact ⟨_, by
    constructor
    · taint_decide
    · decide +kernel⟩

end VG.Proof.Mont.X86.StaticSquare
