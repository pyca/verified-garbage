module
public import VerifiedGarbage.Impl.Bignum.AArch64.Square
public import VerifiedGarbage.Proof.Bignum.AArch64.MontCore

import VerifiedGarbage.Proof.Bignum.AArch64.SquareRaw
import VerifiedGarbage.Proof.Bignum.AArch64.SquareRedc
import VerifiedGarbage.Proof.Bignum.AArch64.SquareFinish
import VerifiedGarbage.Proof.Bignum.AArch64.SquareLayout
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.AArch64.SquareCross
import VerifiedGarbage.Proof.Bignum.AArch64.SquareDiagonalLoop

/-! Structural public state used by the constant-time composition. -/

@[expose] public section

namespace VG.Proof.Bignum.AArch64.Square
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public VG.Proof.Bignum
open VG.Proof.Bignum.AArch64
open VG.Proof.MlKem.AArch64 (Keep)

def GW (L : Ws) (s : State) : Prop := GoodW L s ∧ 8 ≤ L.w

structure SetupCtx (a : Nat) (L : Ws) (s : State) : Prop where
  good : GW L s
  x8 : s.gpr .x8 = off L.B (slot L.w aAcc+16)
  x9 : s.gpr .x9 = off L.B (slot L.w a)
  x10 : s.gpr .x10 = off L.B (slot L.w aN)
  x12 : s.gpr .x12 = BitVec.ofNat 64 L.w
  x7 : s.gpr .x7 = 0

structure RawCtx (L : Ws) (s : State) : Prop where
  good : GW L s
  x8 : s.gpr .x8 = off L.B (slot L.w aAcc+16)
  x10 : s.gpr .x10 = off L.B (slot L.w aN)
  x12 : s.gpr .x12 = BitVec.ofNat 64 L.w
  x7 : s.gpr .x7 = 0
  x16 : s.gpr .x16 = off L.B (slot L.w aAcc+16+16*L.w)

structure RedCtx (L : Ws) (s : State) : Prop where
  good : GW L s
  x8 : s.gpr .x8 = off L.B (slot L.w aTmp)
  x10 : s.gpr .x10 = off L.B (slot L.w aN)
  x12 : s.gpr .x12 = BitVec.ofNat 64 L.w
  x7 : s.gpr .x7 = 0

structure FinCtx (o : Nat) (L : Ws) (s : State) : Prop where
  reduced : RedCtx L s
  x5 : s.gpr .x5 = off L.B (slot L.w o)
  x6 : s.gpr .x6 = off L.B (slot L.w aAcc)

theorem pins_gw : Pins GW [.x0] :=
  fun L s₁ s₂ h₁ h₂ => pins_goodW L s₁ s₂ h₁.1 h₂.1

theorem pins_setup (a : Nat) : Pins (SetupCtx a) [.x0, .x8, .x9, .x10, .x12, .x7] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pins_gw L s₁ s₂ h₁.good h₂.good .x0 (by simp)
  · rw [h₁.x8, h₂.x8]
  · rw [h₁.x9, h₂.x9]
  · rw [h₁.x10, h₂.x10]
  · rw [h₁.x12, h₂.x12]
  · rw [h₁.x7, h₂.x7]

theorem pins_raw : Pins RawCtx [.x0, .x8, .x10, .x12, .x7, .x16] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pins_gw L s₁ s₂ h₁.good h₂.good .x0 (by simp)
  · rw [h₁.x8, h₂.x8]
  · rw [h₁.x10, h₂.x10]
  · rw [h₁.x12, h₂.x12]
  · rw [h₁.x7, h₂.x7]
  · rw [h₁.x16, h₂.x16]

theorem pins_red : Pins RedCtx [.x0] :=
  fun L s₁ s₂ h₁ h₂ => pins_gw L s₁ s₂ h₁.good h₂.good

theorem pins_fin (o : Nat) : Pins (FinCtx o) [.x8, .x10, .x12, .x7, .x5, .x6] := by
  intro L s₁ s₂ h₁ h₂ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h₁.reduced.x8, h₂.reduced.x8]
  · rw [h₁.reduced.x10, h₂.reduced.x10]
  · rw [h₁.reduced.x12, h₂.reduced.x12]
  · rw [h₁.reduced.x7, h₂.reduced.x7]
  · rw [h₁.x5, h₂.x5]
  · rw [h₁.x6, h₂.x6]

theorem setup_ctx {a : Nat} (ha : a < 8) (L : Ws) (s : State) (h : GW L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.squareSetup a)) s (SetupCtx a L) := by
  obtain ⟨⟨mi, hg, hz⟩, hsz⟩ := h
  refine WP.mono (squareSetup_ok hg.scr hg.x0 hg.hdr hz ha)
    fun t ⟨⟨h8, h9, h10, h12, _, h7, hm⟩, k⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr k.wr, (k.gpr .x0 (by decide)).trans hg.x0, hm ▸ hg.hdr⟩, hz⟩, hsz⟩,
    h8, h9, h10, h12, h7⟩

theorem raw_body_ctx {a : Nat} (ha : a < 8) (ha1 : a ≠ aAcc) (ha2 : a ≠ aTmp)
    (L : Ws) (s : State) (h : SetupCtx a L s) :
    WP isa (.seq VG.Impl.Bignum.AArch64.Square.cross VG.Impl.Bignum.AArch64.Square.diagonal) s (RawCtx L) := by
  obtain ⟨⟨mi, hg, hz⟩, hsz⟩ := h.good
  have hn := hg.scr.nowrap
  have hw := goodW_width (show GoodW L s from ⟨mi, hg, hz⟩)
  have hA : slot L.w aAcc+16+8*(2*L.w+2) ≤ L.Z := by
    have := slot_le (w := L.w) (show aTmp < 8 by decide)
    unfold slot aAcc aTmp at *; omega
  have hb : slot L.w a+8*L.w ≤ L.Z := by have := slot_le (w := L.w) ha; omega
  have sb : slot L.w a+8*L.w ≤ slot L.w aAcc+16 ∨
      slot L.w aAcc+16+8*(2*L.w+2) ≤ slot L.w a := by
    have := slot_sep (w := L.w) ha1; have := slot_sep (w := L.w) ha2
    unfold slot aAcc aTmp at *; omega
  refine WP.seq (WP.mono (cross_ok hg.scr h.x8 h.x9 h.x12 h.x7 (by omega) hw hA hb sb)
    fun u ⟨_, hou, _, ku⟩ => ?_)
  refine WP.mono (diagonal_ok (hg.scr.congr ku.wr)
    ((ku.gpr .x8 (by decide)).trans h.x8) ((ku.gpr .x9 (by decide)).trans h.x9)
    ((ku.gpr .x12 (by decide)).trans h.x12) ((ku.gpr .x7 (by decide)).trans h.x7)
    (by omega) hw (by omega) hb (by omega)) fun t ⟨_, hot, h16, kt⟩ => ?_
  have kAll := ku.trans kt
  have ho := hou.trans (hot.mono (o' := slot L.w aAcc+16)
    (n' := 8*(2*L.w+2)) (Nat.le_refl _) (by omega))
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kAll.wr, (kAll.gpr .x0 (by decide)).trans hg.x0,
    (scratch_arrays ho).hdr hg.hdr⟩, hz⟩, hsz⟩,
    (kAll.gpr .x8 (by decide)).trans h.x8,
    (kAll.gpr .x10 (by decide)).trans h.x10,
    (kAll.gpr .x12 (by decide)).trans h.x12,
    (kAll.gpr .x7 (by decide)).trans h.x7, h16⟩

theorem redc_ctx (L : Ws) (s : State) (h : RawCtx L s) :
    WP isa VG.Impl.Bignum.AArch64.Square.redc s (RedCtx L) := by
  obtain ⟨⟨mi, hg, hz⟩, hsz⟩ := h.good
  have hw := goodW_width (show GoodW L s from ⟨mi, hg, hz⟩)
  refine WP.mono (redc_ok hg.scr hz h.x8 h.x10 h.x12 (minv := s.gpr .x15) rfl
    h.x7 (by omega) hw) fun t ⟨_, ho, h8, h10, h12, h7, kt⟩ => ?_
  exact ⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    (scratch_arrays ho).hdr hg.hdr⟩, hz⟩, hsz⟩, h8, h10, h12, h7⟩

theorem finish_bases_ctx {o : Nat} (ho : o < 8) (L : Ws) (s : State) (h : RedCtx L s) :
    WP isa (.block (VG.Impl.Bignum.AArch64.Square.finishBases o)) s (FinCtx o L) := by
  obtain ⟨⟨mi, hg, hz⟩, hsz⟩ := h.good
  refine WP.mono (finishBases_ok hg.scr hg.x0 hg.hdr hz ho) fun t ⟨⟨h5, h6, hm⟩, kt⟩ => ?_
  exact ⟨⟨⟨⟨mi, ⟨hg.scr.congr kt.wr, (kt.gpr .x0 (by decide)).trans hg.x0,
    hm ▸ hg.hdr⟩, hz⟩, hsz⟩, (kt.gpr .x8 (by decide)).trans h.x8,
    (kt.gpr .x10 (by decide)).trans h.x10, (kt.gpr .x12 (by decide)).trans h.x12,
    (kt.gpr .x7 (by decide)).trans h.x7⟩, h5, h6⟩

end VG.Proof.Bignum.AArch64.Square
