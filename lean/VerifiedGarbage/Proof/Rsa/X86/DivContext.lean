module
public import VerifiedGarbage.Proof.Mont.X86.Words
public import VerifiedGarbage.Proof.Mont.Words32

import VerifiedGarbage.Proof.Rsa.WordRanges
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.InstancePriority
import Std.Data.DTreeMap.Internal.Operations
import VerifiedGarbage.Proof.Framework.GetElem
import VerifiedGarbage.Proof.Framework.PlainSimp

/-! # Public geometry for fixed-width native RSA division -/

@[expose] public section
namespace VG.Proof.Rsa.X86.Div
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86

structure Geometry where
  base : Addr
  size : Nat
  offsets : Fin 4 → Nat
  n : Nat

def Geometry.words (g : Geometry) (i : Fin 4) : Nat := if i = 0 then g.n else g.n + 1

def Geometry.ranges (g : Geometry) : List (Nat × Nat) :=
  [(g.offsets 0, 4 * g.n), (g.offsets 1, 4 * (g.n + 1)), (g.offsets 3, 4 * (g.n + 1))]

def Geometry.value (g : Geometry) (m : Mem) (i : Fin 4) : Nat :=
  val32 m g.base (g.offsets i) (g.words i)

structure Context (g : Geometry) (s : State) : Prop where
  workspace : Scr s g.base g.size
  positive : 0 < g.n
  bound : g.n < 2 ^ 24
  fits : ∀ i, g.offsets i + 4 * g.words i ≤ g.size
  separate : ∀ i j, i ≠ j →
    g.offsets i + 4 * g.words i ≤ g.offsets j ∨ g.offsets j + 4 * g.words j ≤ g.offsets i

theorem Context.after {g : Geometry} {s t : State} {rs : List Reg} (h : Context g s)
    (rest : Keeps rs s t) (edi : .edi ∉ rs := by decide) (esp : .esp ∉ rs := by decide) : Context g t :=
  { h with workspace := h.workspace.of_keeps rest edi esp }

theorem Context.divisor_frame {g : Geometry} {s : State} {m : Mem} (h : Context g s)
    (frame : Outs g.base g.ranges s.mem m) : g.value m 2 = g.value s.mem 2 := by
  apply frame.val32
  · intro r hr
    simp only [Geometry.ranges, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.separate 2 0 (by decide)
    · exact h.separate 2 1 (by decide)
    · exact h.separate 2 3 (by decide)
  · have := h.fits 2
    have := h.workspace.nowrap
    omega

theorem quotientShift_frame {g : Geometry} {m m' : Mem}
    (frame : Outs g.base [(g.offsets 0, 4 * g.n), (g.offsets 3, 4 * g.n)] m m') :
    Outs g.base g.ranges m m' := by
  apply outs_cover frame
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [Geometry.ranges], Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(g.offsets 3, 4 * (g.n + 1)), by simp [Geometry.ranges], Nat.le_refl _, by omega⟩
end VG.Proof.Rsa.X86.Div
