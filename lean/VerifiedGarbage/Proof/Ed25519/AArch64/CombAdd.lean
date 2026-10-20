module

import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Step
public import VerifiedGarbage.Proof.Ed25519.AArch64.Point64.Fn
public import VerifiedGarbage.Impl.Ed25519.AArch64.Comb
public import VerifiedGarbage.Proof.X25519.AArch64.AltLadder.Env
import VerifiedGarbage.Proof.Ed25519.AArch64.CounterKeep
import VerifiedGarbage.Proof.Framework.Block

/-!
# The comb's addition, on the `_alt` operations

`combAdd` adds the affine entry in slots 4–6 to the accumulator in slots 0–3
with `addAffineOps`' formula (`mixedResult`), on the operations of `AltOps`
(`combAdd_ok`). Its sums and differences need inputs below `2·p`, which the
accumulator's coordinates are, as products of `mul_4`, between additions
(`AccBel`).
-/

@[expose] public section

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.X25519.AArch64.Alt (AltOp)
open VG.Proof.X25519.AArch64.AltLadder (P2 mulE addE addE1 subE fr x17_ok altClob_sub)

variable {large : Bool}

/-- The accumulator's coordinates (slots 0–3) are below `2·p`. -/
def AccBel (m : Mem) (base : Addr) : Prop := ∀ i : Slot, i.val < 4 → fe m base (offset i) < P2

theorem _root_.VG.Proof.X25519.AArch64.Alt.AltOp.keep {base : Addr} {o : Slot} {s t : State} (h : AltOp base (offset o) s t)
    (ho : o.val ≤ 13) : Keep base s t :=
  ⟨fun r hr => h.gpr r (fun hm => hr (altClob_sub r hm)), h.rd, h.wr, h.sp,
    h.mem.mono (by simp only [offset]; omega) (by simp only [offset]; omega)⟩

theorem _root_.VG.Proof.X25519.AArch64.Alt.AltOp.x17 {base : Addr} {o : Nat} {s t : State} (h : AltOp base o s t)
    (hz : s.gpr .x17 = 0) : t.gpr .x17 = 0 :=
  (h.gpr _ (by decide)).trans hz

/-- **The addition**: slots 0–3 hold `mixedResult` of the accumulator and the entry, below
`2·p`; only slots 0–3 and 7–12 change. -/
theorem combAdd_ok {s : State} {base : Addr} (hs : Scr s base large) (hb : AccBel s.mem base) :
    WP isa (.block combAdd) s fun t => Keep base s t ∧ AccBel t.mem base ∧
      point (env t.mem base) 0 1 2 3 = Point64.mixedResult (env s.mem base 0) (env s.mem base 1)
        (env s.mem base 2) (env s.mem base 3) (env s.mem base 4) (env s.mem base 5)
        (env s.mem base 6) ∧
      ∀ i : Slot, (4 ≤ i.val ∧ i.val < 7) ∨ 13 ≤ i.val → fe t.mem base (offset i) = fe s.mem base (offset i) := by
  simp only [combAdd, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (x17_ok s) fun a ⟨za, ka⟩ => ?_
  have k0 : Keep base s a := Keep.of_keeps ka (by decide)
  have ha := k0.scr hs
  have ea : env a.mem base = env s.mem base := by rw [ka.mem]
  have fa : ∀ i, fe a.mem base (offset i) = fe s.mem base (offset i) := fun i => by rw [ka.mem]
  -- t0 = 2z₁, t1 = y₁ - x₁, t2 = y₁ + x₁
  rw [WP.block_append_iff]
  refine WP.mono (addE ha 7 2 2 (by decide) (by decide) (by decide) za
    (by rw [fa]; exact hb 2 (by decide)) (by rw [fa]; exact hb 2 (by decide))) fun b1 ⟨h1, e1⟩ => ?_
  rw [ea] at e1
  have s1 := (h1.keep (by decide)).scr ha
  have z1 := h1.x17 za
  rw [WP.block_append_iff]
  refine WP.mono (subE s1 8 1 0 (by decide) (by decide) (by decide) z1
    (by rw [fr h1 0 (by decide), fa]; exact hb 0 (by decide))) fun b2 ⟨h2, e2⟩ => ?_
  rw [e1] at e2
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e2
  have s2 := (h2.keep (by decide)).scr s1
  have z2 := h2.x17 z1
  rw [WP.block_append_iff]
  refine WP.mono (addE s2 9 1 0 (by decide) (by decide) (by decide) z2
    (by rw [fr h2 1 (by decide), fr h1 1 (by decide), fa]; exact hb 1 (by decide))
    (by rw [fr h2 0 (by decide), fr h1 0 (by decide), fa]; exact hb 0 (by decide)))
    fun b3 ⟨h3, e3⟩ => ?_
  rw [e2] at e3
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e3
  have s3 := (h3.keep (by decide)).scr s2
  have z3 := h3.x17 z2
  -- t3 = w₁ · kxy, t1 = t1 · ymx, t2 = t2 · xpy
  rw [WP.block_append_iff]
  refine WP.mono (mulE s3 10 3 6 (by decide) (by decide) (by decide) z3) fun b4 ⟨h4, l4, e4⟩ => ?_
  rw [e3] at e4
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e4
  have s4 := (h4.keep (by decide)).scr s3
  have z4 := h4.x17 z3
  rw [WP.block_append_iff]
  refine WP.mono (mulE s4 8 8 4 (by decide) (by decide) (by decide) z4) fun b5 ⟨h5, l5, e5⟩ => ?_
  rw [e4] at e5
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e5
  have s5 := (h5.keep (by decide)).scr s4
  have z5 := h5.x17 z4
  rw [WP.block_append_iff]
  refine WP.mono (mulE s5 9 9 5 (by decide) (by decide) (by decide) z5) fun b6 ⟨h6, l6, e6⟩ => ?_
  rw [e5] at e6
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e6
  have s6 := (h6.keep (by decide)).scr s5
  have z6 := h6.x17 z5
  -- t4 = t0 - t3, t0 = t0 + t3, t5 = t2 - t1, t1 = t2 + t1
  have l10 : fe b6.mem base (offset 10) < P2 := by
    rw [fr h6 10 (by decide), fr h5 10 (by decide)]; exact l4
  rw [WP.block_append_iff]
  refine WP.mono (subE s6 11 7 10 (by decide) (by decide) (by decide) z6 l10) fun b7 ⟨h7, e7⟩ => ?_
  rw [e6] at e7
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e7
  have s7 := (h7.keep (by decide)).scr s6
  have z7 := h7.x17 z6
  rw [WP.block_append_iff]
  refine WP.mono (addE1 s7 7 7 10 (by decide) (by decide) (by decide) z7
    (by rw [fr h7 10 (by decide)]; exact l10)) fun b8 ⟨h8, e8⟩ => ?_
  rw [e7] at e8
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e8
  have s8 := (h8.keep (by decide)).scr s7
  have z8 := h8.x17 z7
  have l8 : fe b8.mem base (offset 8) < P2 := by
    rw [fr h8 8 (by decide), fr h7 8 (by decide), fr h6 8 (by decide)]; exact l5
  have l9 : fe b8.mem base (offset 9) < P2 := by
    rw [fr h8 9 (by decide), fr h7 9 (by decide)]; exact l6
  rw [WP.block_append_iff]
  refine WP.mono (subE s8 12 9 8 (by decide) (by decide) (by decide) z8 l8) fun b9 ⟨h9, e9⟩ => ?_
  rw [e8] at e9
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e9
  have s9 := (h9.keep (by decide)).scr s8
  have z9 := h9.x17 z8
  rw [WP.block_append_iff]
  refine WP.mono (addE s9 8 9 8 (by decide) (by decide) (by decide) z9
    (by rw [fr h9 9 (by decide)]; exact l9) (by rw [fr h9 8 (by decide)]; exact l8))
    fun b10 ⟨h10, e10⟩ => ?_
  rw [e9] at e10
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e10
  have s10 := (h10.keep (by decide)).scr s9
  have z10 := h10.x17 z9
  -- z₃ = t4 · t0, x₃ = t5 · t4, y₃ = t0 · t1, w₃ = t5 · t1
  rw [WP.block_append_iff]
  refine WP.mono (mulE s10 2 11 7 (by decide) (by decide) (by decide) z10) fun b11 ⟨h11, l11, e11⟩ => ?_
  rw [e10] at e11
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e11
  have s11 := (h11.keep (by decide)).scr s10
  have z11 := h11.x17 z10
  rw [WP.block_append_iff]
  refine WP.mono (mulE s11 0 12 11 (by decide) (by decide) (by decide) z11) fun b12 ⟨h12, l12, e12⟩ => ?_
  rw [e11] at e12
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e12
  have s12 := (h12.keep (by decide)).scr s11
  have z12 := h12.x17 z11
  rw [WP.block_append_iff]
  refine WP.mono (mulE s12 1 7 8 (by decide) (by decide) (by decide) z12) fun b13 ⟨h13, l13, e13⟩ => ?_
  rw [e12] at e13
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e13
  have s13 := (h13.keep (by decide)).scr s12
  have z13 := h13.x17 z12
  refine WP.mono (mulE s13 3 12 8 (by decide) (by decide) (by decide) z13) fun t ⟨h14, l14, e14⟩ => ?_
  rw [e13] at e14
  simp only [Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte] at e14
  have kt : Keep base s t := k0.trans (h1.keep (by decide))
    |>.trans (h2.keep (by decide))
    |>.trans (h3.keep (by decide))
    |>.trans (h4.keep (by decide))
    |>.trans (h5.keep (by decide))
    |>.trans (h6.keep (by decide))
    |>.trans (h7.keep (by decide))
    |>.trans (h8.keep (by decide))
    |>.trans (h9.keep (by decide))
    |>.trans (h10.keep (by decide))
    |>.trans (h11.keep (by decide))
    |>.trans (h12.keep (by decide))
    |>.trans (h13.keep (by decide))
    |>.trans (h14.keep (by decide))
  refine ⟨kt, ?_, ?_, ?_⟩
  · intro i hi
    have hc : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 :=
      (by decide : ∀ i : Slot, i.val < 4 → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) i hi
    rcases hc with rfl | rfl | rfl | rfl
    · rw [fr h14 0 (by decide), fr h13 0 (by decide)]; exact l12
    · rw [fr h14 1 (by decide)]; exact l13
    · rw [fr h14 2 (by decide), fr h13 2 (by decide), fr h12 2 (by decide)]; exact l11
    · exact l14
  · rw [e14]
    simp only [point, Function.update_apply, Fin.isValue, Fin.reduceEq, ↓reduceIte]
    rfl
  · intro i hi
    have n : ∀ o : Slot, (o.val < 4 ∨ (7 ≤ o.val ∧ o.val ≤ 12)) → i ≠ o :=
      fun o ho e => by have := congrArg Fin.val e; omega
    rw [fr h14 i (n 3 (by decide)), fr h13 i (n 1 (by decide)), fr h12 i (n 0 (by decide)),
      fr h11 i (n 2 (by decide)), fr h10 i (n 8 (by decide)), fr h9 i (n 12 (by decide)),
      fr h8 i (n 7 (by decide)), fr h7 i (n 11 (by decide)), fr h6 i (n 9 (by decide)),
      fr h5 i (n 8 (by decide)), fr h4 i (n 10 (by decide)), fr h3 i (n 9 (by decide)),
      fr h2 i (n 8 (by decide)), fr h1 i (n 7 (by decide)), fa]

end VG.Proof.Ed25519.AArch64
