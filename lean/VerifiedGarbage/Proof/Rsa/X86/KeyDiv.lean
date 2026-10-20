module
public import VerifiedGarbage.Proof.Rsa.X86.DivContext
public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Rsa.X86.KeyWs

import VerifiedGarbage.Proof.Rsa.X86.DivLoop
import VerifiedGarbage.Proof.Rsa.WordRanges
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Push
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import Mathlib.Tactic.ToAdditive
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.PlainSimp
import VerifiedGarbage.Proof.Rsa.KeyMath

/-! # Fixed-count division on key-workspace arrays -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Keys
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Rsa.X86.Keys hiding slot

def divGeometry (B : Addr) (Z w : Nat) (ids : Fin 4 → Nat) : Div.Geometry :=
  ⟨B, Z, fun i => arr w (ids i), w⟩

theorem div_context {s : State} {B : Addr} {Z w N : Nat} {ids : Fin 4 → Nat}
    (h : Ws s B Z w N) (fits : ∀ i, ids i < N) (distinct : ∀ i j, i ≠ j → ids i ≠ ids j) :
    Div.Context (divGeometry B Z w ids) s := by
  refine ⟨h.workspace, h.wpos, by change w < 2 ^ 24; have := h.wle; omega, ?_, ?_⟩
  · intro i
    have fit := h.arr_fit (fits i)
    change arr w (ids i) + 4 * (if i = 0 then w else w + 1) ≤ Z
    unfold S at fit
    split <;> omega
  · intro i j ne
    have sep := arr_disj (w := w) (distinct i j ne)
    change arr w (ids i) + 4 * (if i = 0 then w else w + 1) ≤ arr w (ids j) ∨
      arr w (ids j) + 4 * (if j = 0 then w else w + 1) ≤ arr w (ids i)
    unfold S at sep
    split <;> split <;> omega

theorem div_ok {s : State} {B : Addr} {Z w N : Nat} {ids : Fin 4 → Nat}
    (h : Ws s B Z w N) (fits : ∀ i, ids i < N) (distinct : ∀ i j, i ≠ j → ids i ≠ ids j)
    (top : w32 s.mem B (arr w (ids 2) + 4 * w) = 0) :
    WP isa (VG.Impl.Rsa.X86.Div.code w (arr w (ids 0)) (arr w (ids 1)) (arr w (ids 2)) (arr w (ids 3))) s
      fun t => Ws t B Z w N ∧ Keep B w [ids 0, ids 1, ids 3] [] s.mem t.mem ∧
        Keeps [.eax, .ecx, .edx, .ebp, .ebx, .esi] s t ∧
        (0 < num s.mem B w (ids 2) →
          num t.mem B w (ids 0) = num s.mem B w (ids 0) / num s.mem B w (ids 2) ∧
          num t.mem B w (ids 1) = num s.mem B w (ids 0) % num s.mem B w (ids 2)) := by
  refine WP.mono (Div.code_ok (div_context h fits distinct)) ?_
  rintro t ⟨_, frame, rest, value⟩
  refine ⟨h.rest rest, ?_, rest, ?_⟩
  · apply outs_cover frame
    intro r hr
    simp only [divGeometry, Div.Geometry.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨(arr w (ids 0), S w), by simp [ranges], Nat.le_refl _, by unfold S; omega⟩
    · exact ⟨(arr w (ids 1), S w), by simp [ranges], Nat.le_refl _, by unfold S; omega⟩
    · exact ⟨(arr w (ids 3), S w), by simp [ranges], Nat.le_refl _, by unfold S; omega⟩
  · intro positive
    have divisor : (divGeometry B Z w ids).value s.mem 2 = num s.mem B w (ids 2) := by
      change val32 s.mem B (arr w (ids 2)) (w + 1) = _
      rw [val32_succ, top, Nat.mul_zero, Nat.add_zero]
    rw [divisor] at value
    obtain ⟨rem, quot⟩ := value positive (val32_lt _ _ _ _)
    refine ⟨quot, ?_⟩
    change val32 t.mem B (arr w (ids 1)) (w + 1) =
      num s.mem B w (ids 0) % num s.mem B w (ids 2) at rem
    rw [val32_succ] at rem
    have small := Nat.mod_lt (num s.mem B w (ids 0)) positive
    have bound := val32_lt s.mem B (arr w (ids 2)) w
    have topZero : w32 t.mem B (arr w (ids 1) + 4 * w) = 0 := by
      by_contra ne
      have ge := Nat.mul_le_mul_left (2 ^ (32 * w))
        (show 1 ≤ w32 t.mem B (arr w (ids 1) + 4 * w) by omega)
      simp only [Nat.mul_one] at ge
      change num s.mem B w (ids 2) < _ at bound
      omega
    rw [topZero, Nat.mul_zero, Nat.add_zero] at rem
    exact rem
end VG.Proof.Rsa.X86.Keys
