module
public import VerifiedGarbage.Proof.Framework.X86.Spill
public import VerifiedGarbage.Proof.Weierstrass.PointContract
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
public import VerifiedGarbage.Impl.Dsa.X86.Entry
public import VerifiedGarbage.Proof.Dsa.X86.Pointer
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Dsa.X86.SavedFrame
import VerifiedGarbage.Proof.Dsa.X86.HeaderFrame
import VerifiedGarbage.Proof.Dsa.X86.Layout

/-! # Precise header frames for packed-key pointer installation -/

@[expose] public section
namespace VG.Proof.Dsa.X86
open VG VG.X86 VG.X86.Spill VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86

def keyPointerRanges : List (Nat × Nat) :=
  [(Layout.field .q, 4), (Layout.field .g, 4), (Layout.field .y, 4), (Layout.field .x, 4)]

theorem keyPointerFrame_header {base : Addr} {m m' : Mem} (O : Outs base keyPointerRanges m m') :
    Outside base 8192 64 m m' := by
  intro a ha
  apply O a
  intro pair hp
  simp only [keyPointerRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp only [Layout.field] <;> omega

theorem keyPointerFrame_field {base : Addr} {s t : State} {f : Field}
    (O : Outs base keyPointerRanges s.mem t.mem) (hf : f ∉ [.q, .g, .y, .x]) :
    pointerValue base t (.input f) = pointerValue base s (.input f) := by
  have B := VG.Proof.Dsa.X86.Layout.field_bounds f
  have H : val32 t.mem base (Layout.field f) 1 = val32 s.mem base (Layout.field f) 1 := by
    apply O.val32
    · intro pair hp
      simp only [keyPointerRanges, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · exact field_separate (f := f) (other := .q) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .g) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .y) (by intro he; subst f; exact hf (by simp))
      · exact field_separate (f := f) (other := .x) (by intro he; subst f; exact hf (by simp))
    · have H : Layout.saved = 8256 := rfl
      omega
  apply BitVec.eq_of_toNat_eq
  simpa only [val32, w32, pointerValue, Nat.mul_zero, Nat.add_zero] using H

theorem saved_header {base : Addr} {m m' : Mem} {regs : Reg → BitVec 32}
    (O : Outside base 8192 64 m m') (S : Saved m (off base) regs Entry.savedRegisters) :
    Saved m' (off base) regs Entry.savedRegisters := by
  intro pair hp
  have B := saved_bounds hp
  have H := O.val32 (d := pair.2) (k := 1) (.inr (by omega)) (by omega)
  have V : m'.readW (off base pair.2) 32 = m.readW (off base pair.2) 32 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [val32, w32, Nat.mul_zero, Nat.add_zero] using H
  exact V.trans (S pair hp)

end VG.Proof.Dsa.X86
