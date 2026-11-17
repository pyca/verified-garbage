module

import VerifiedGarbage.Proof.Ecdsa.X86.Inv
public import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Weierstrass.X86.Rep
import VerifiedGarbage.Proof.Ecdsa.Sign
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
import VerifiedGarbage.Proof.Ecdsa.X86.PtLays
import VerifiedGarbage.Proof.Ecdsa.X86.Scalar
import VerifiedGarbage.Proof.Ecdsa.X86.Middle
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Setup
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderPCall
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP
import VerifiedGarbage.Proof.Framework.X86.CallWith
import VerifiedGarbage.Proof.Framework.Contract

/-! ### `Ecdsa.X86.QMul`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.X86.MulFn`, which only this module used -/

section

/-!
# `vg_<curve>_mul` on x86 (32-bit): the body

`mulBody` (`Impl/Ecdsa/X86.lean`) makes the table of the bits of the
number at `K`'s slot, copies `Q` from `R`'s first two slots to `ACC` and
`PT`, sets `R = O` from zero and one, and runs the ladder from the point at
`ACC`, `PT`, `ONEP` (`c.mulLadder`, `ladAt c ACC PT`). For any invariant `Q`
of the ladder from the point at `RX`, `RY`, `ONEP` (`Step` of `ladAt c RX
RY`, which the copies carry to the ladder's point) that accepts `O`, `Q 0`
accepts what `R` holds at the end, and the body writes only what the ladder
writes, `ACC`, `PT` and the table of bits (`mulBody_ok`). As on PPC64LE
(`Proof/Ecdsa/PPC64LE/LadPow.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- The signature's ladder from the point at `gx`, `gy`, `ONEP`. -/
abbrev ladAt (c : Cfg) (gx gy : Nat) : LadderCfg := { c.ladderCfg with G := c.pt gx gy ONEP }

theorem mulLadder_eq (c : Cfg) : c.mulLadder = ladAt c ACC PT := rfl

/-- `Step` depends only on what the slots of `a`, `3b` and the point hold. -/
theorem step_congr {L L' : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hb : L'.nbits = L.nbits)
    (ha : tmv C L'.M.n base s' L'.S.a = tmv C L.M.n base s L.S.a)
    (h3 : tmv C L'.M.n base s' L'.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L'.M.n base s' L'.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L'.M.n base s' L'.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L'.M.n base s' L'.G.z = tmv C L.M.n base s L.G.z)
    {a0 : Bool} (h : Step L C base s k Q a0) : Step L' C base s' k Q a0 := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'
  rw [ha, h3] at h2 h3'
  rw [hx, hy, hz] at h3'
  exact h j (hb ▸ hj) X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'

/-- `[o] = [a]`, on numbered slots. -/
theorem copySl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o a : Nat}
    (ho : o < 45) (ha : a < 45) (hoa : o ≠ a) :
    WP isa (.block (copy (2 * c.n) (c.sl o) (c.sl a))) s fun s' =>
      sv c base s' o = sv c base s a ∧ Keeps [.eax] s s' ∧
      Outside base (c.sl o) (8 * c.n) s.mem s'.mem := by
  have := sl_apart c hoa
  have := sl_le c hc.n10 ho
  have := sl_le c hc.n10 ha
  refine WP.mono (copy_ok (2 * c.n) hs (by omega_arith) (by omega_using [this]) (by omega_arith)) fun s' ⟨e, k, O⟩ => ⟨?_, k, ?_⟩
  · show wordsVal _ _ _ _ = wordsVal _ _ _ _
    rw [wordsVal_eq_val32, wordsVal_eq_val32, e]
  · rw [show 8 * c.n = 4 * (2 * c.n) by omega_using []]; exact O

/-- A slot's number apart from a slot written at another. -/
theorem sv_outside {base : Addr} {m m' : Mem} {j i : Nat} (h7 : c.n < 10)
    (O : Outside base (c.sl j) (8 * c.n) m m') (hi : i < 45) (hij : i ≠ j) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
  O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; have : size = 8192 := rfl; omega_arith)

/-! ## The ladder's slots -/

theorem ladLayM (hc : CfgOk c) : LadLay c.mulLadder size := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, ACC, PT, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega_arith, show 64 * c.n < 2 ^ 16 by omega_arith⟩,
    bitsAt_le c h7 (j := 0) (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, B3P, ACC, PT, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, B3P, ACC, PT, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (by decide)
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      obtain hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c (i := TMP) (by decide) 0 0)

theorem ladWkM (hc : CfgOk c) : LadWk c.mulLadder c.SP c.C.p size c.wk where
  fn := hc.fp.2.2
  k := hc.fp.1
  fm := hc.fp.2.1
  size := rfl
  own := rfl
  sl := by
    have e : ladSlots c.mulLadder = [AP, B3P, ACC, PT, ONEP, RX, RY, RZ, T0, T1, T2, T3,
      T4, T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl
    rw [e]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have : ∀ i ∈ [AP, B3P, ACC, PT, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ],
      i < 45 := by decide
    exact sl_below_wk c (this i hi)
  mo := sl_below_wk c (i := MP) (by decide)
  tmp := sl_below_wk c (i := TMP) (by decide)
  bits := wk_below_bits c 0
  bits_top := by have := bitsAt_le c hc.n10 (j := 0) (by decide); exact this

/-- What every signature's ladder writes (for any point: `ladWx` does not
depend on it). -/
theorem ladWx_at (c : Cfg) (gx gy : Nat) : ladWx (ladAt c gx gy) c.wk = slW c [RX, RY, RZ, T0, T1, T2,
    T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] ++ wkW c := rfl

/-! ## The body -/

/-- What `mulBody` writes besides the ladder: `ACC`, `PT` and the table of
the bits of `k`. -/
abbrev mulBX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n)]

/-- What `mulBody` writes: the ladder's and `mulBX`. -/
abbrev mulBW (c : Cfg) : List (Nat × Nat) := ladWx c.mulLadder c.wk ++ mulBX c

/-- `mulBody`: for any invariant `Q` of the ladder from the point at `RX`,
`RY`, `ONEP` that accepts `O` (as zero and one hold it), for the scalar at
`K`'s slot, `Q 0` accepts what `R` holds at the end; only `powClob` and
`mulBW` change. -/
theorem mulBody_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulBody s fun s' => Keeps powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (sl_le c h7 (i := K) (by decide)) (bitsAt_le c h7 (j := 0) (by decide))
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0; omega_arith))) fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keeps K₁ (by decide)
  obtain e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    sv_unch O₁.unch h7 hn hi (apart_tbl hi 0)
  -- The copies.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := ACC) (a := RX) (by decide) (by decide) (by decide))
    fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := PT) (a := RY) (by decide) (by decide) (by decide))
    fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₃ (o := RX) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  obtain hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₄ (o := RY) (a := ONEP) (by decide) (by decide) (by decide))
    fun s₅ ⟨x₅, k₅, O₅⟩ => ?_)
  obtain hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (copySl_ok hc hs₅ (o := RZ) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨x₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keeps k₆ (by decide)
  obtain K₁₆ : Keeps powClob s s₆ :=
    (K₁.mono (by decide)).trans ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆ |>.mono (by decide))
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, RX, RY, RZ] → sv c base s₆ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [o O₆ hi hl.2.2.2.2, o O₅ hi hl.2.2.2.1, o O₄ hi hl.2.2.1, o O₃ hi hl.2.1, o O₂ hi hl.1, e₁ hi]
  obtain acc₆ : sv c base s₆ ACC = sv c base s RX := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), x₂, e₁ (by decide)]
  obtain pt₆ : sv c base s₆ PT = sv c base s RY := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), x₃,
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rx₆ : sv c base s₆ RX = sv c base s ZERO := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), x₄, o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain ry₆ : sv c base s₆ RY = sv c base s ONEP := by
    rw [o O₆ (by decide) (by decide), x₅, o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain rz₆ : sv c base s₆ RZ = sv c base s ZERO := by
    rw [x₆, o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  obtain U₁₆ : Unch base (mulBX c ++ slW c [RX, RY, RZ]) s.mem s₆.mem := by
    have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    refine this.mono fun w hw => ?_
    simp only [slW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.map_cons,
      List.map_nil] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  obtain T₆ : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    obtain U : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem := by
      have := O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch)))
      exact this.mono fun w hw => by simpa using hw
    rw [tbl_unch U h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t), T₁ t ht]
  obtain tv : ∀ {i j : Nat}, sv c base s₆ i = sv c base s j →
      tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
    show toM _ _ (sv c base s₆ _) = toM _ _ (sv c base s _); rw [h]
  obtain hstep₆ : Step c.mulLadder c.C base s₆ (sv c base s K) Q :=
    step_congr (L := ladAt c RX RY) (L' := c.mulLadder) rfl (tv (e₆ (by decide) (by decide))) (tv (e₆ (by decide) (by decide)))
      (tv acc₆) (tv pt₆) (tv (e₆ (by decide) (by decide))) hstep
  obtain hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.mulLadder.M.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, ACC, PT, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₆ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [e₆ (by decide) (by decide)]; exact hap
    · rw [e₆ (by decide) (by decide)]; exact hb3
    · rw [acc₆]; exact hqx
    · rw [pt₆]; exact hqy
    · rw [e₆ (by decide) (by decide)]; exact hone
    · rw [rx₆]; exact hzero
    · rw [ry₆]; exact hone
    · rw [rz₆]; exact hzero
  obtain hR : Q c.mulLadder.nbits (tmv c.C c.n base s₆ c.mulLadder.R.x)
      (tmv c.C c.n base s₆ c.mulLadder.R.y) (tmv c.C c.n base s₆ c.mulLadder.R.z) := by
    show Q _ (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY)) (tmv c.C c.n base s₆ (c.sl RZ))
    rw [tv rx₆, tv ry₆, tv rz₆]; exact hO
  refine WP.mono (ladder_ok (ladLayM hc) (ladWkM hc) hpR hs₆
    (modP_of hc ((e₆ (i := MP) (by decide) (by decide)).trans hmp)) hlt hstep₆ hR
    (fun t ht => T₆ t ht)) fun s₇ ⟨K₇, U₇, _, L₇, R₇⟩ => ⟨K₁₆.trans K₇, ?_, L₇, R₇⟩
  refine (U₁₆.trans U₇).mono fun w hw => ?_
  simp only [mulBW, List.mem_append] at hw ⊢
  rcases hw with (hw | hw) | hw
  · exact .inr hw
  · refine .inl ?_
    rw [mulLadder_eq, ladWx_at]
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    obtain hi' : i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, hi', rfl⟩)
  · exact .inl hw

/-! ## The function -/

/-- What `vg_<curve>_mul` writes: `mulBW` and where it keeps the callee-saved
registers. -/
abbrev mulFW (c : Cfg) : List (Nat × Nat) := mulBW c ++ [(c.sl nslots, 16)]

/-- The callee-saved registers' words lie past the numbered slots, below the
field arithmetic's own working space. -/
theorem save_le_wk (h7 : c.n < 10) : c.sl nslots + 16 ≤ c.wk := by
  rw [sl_eq, wk_eq]; simp only [nslots]; omega_arith

/-- The callee-saved registers' words are apart from what the body writes. -/
theorem save_apart (h7 : c.n < 10) {d : Nat} (hd : c.sl nslots ≤ d) (hd' : d + 4 ≤ c.sl nslots + 16) :
    ∀ w ∈ mulBW c, d + 4 ≤ w.1 ∨ w.1 + w.2 ≤ d := by
  intro w hw
  obtain hwk := save_le_wk (c := c) h7
  have := wk_own c
  simp only [mulBW, mulBX, List.mem_append, mulLadder_eq, ladWx_at] at hw
  rcases hw with (hw | hw) | (hw | hw)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (j := nslots) (i := i) ((by decide : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
      T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP], i < nslots) i hi)
    exact .inr (by dsimp only; omega_arith)
  · simp only [wkW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inl (by dsimp only; omega_arith)
    · exact .inl (by dsimp only; omega_arith)
  · simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact .inr (by have := sl_lt c (i := ACC) (j := nslots) (by decide); dsimp only; omega_arith)
    · exact .inr (by have := sl_lt c (i := PT) (j := nslots) (by decide); dsimp only; omega_arith)
  · rw [List.mem_singleton.mp hw]
    exact .inl (by have := wk_below_bits c 0; dsimp only; omega_arith)

/-- `[eax + o + d] = r` for the callee-saved registers, with `eax` the
working space. -/
theorem mulSaves_ok {s : State} {base : Addr} {o : Nat} (ho : o + 16 ≤ size)
    (hb : (s.gpr .eax).setWidth 64 = base) (hfit : (s.gpr .eax).toNat + size ≤ 2 ^ 32)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block ((Cfg.saved.map fun (r, d) => (r, o + d)).map fun (r, d) => .store (at_ .eax d) r)) s
      fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base o 16 s.mem s'.mem ∧
        ∀ rd ∈ Cfg.saved, s'.mem.readW (off base (o + rd.2)) 32 = s.gpr rd.1 := by
  have hsz : size = 8192 := rfl
  obtain hea : ∀ (t : State) (d : Nat), t.gpr .eax = s.gpr .eax → d < size → t.ea (at_ .eax d) = off base d :=
    fun t d ht hd => by
      show addr (t.gpr .eax) d = _
      rw [ht, addr_eq (by omega_arith), hb]
  obtain hin : ∀ (t : State) (d : Nat), t.wr = s.wr → d + 4 ≤ size → InRegions t.wr (off base d) 4 :=
    fun t d ht hd => by rw [ht]; exact ⟨_, hw, Offset.contains_base base (by omega_arith) (by omega_arith)⟩
  obtain hbn : base.toNat + size ≤ 2 ^ 32 := by
    rw [← hb, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega_arith)]; exact hfit
  simp only [Cfg.saved, List.map_cons, List.map_nil]
  refine wp_storeS (hea s (o + 0) rfl (by omega_arith)) (hin s (o + 0) rfl (by omega_arith)) fun s₁ m₁ => ?_
  refine wp_storeS (hea s₁ (o + 4) (by rw [m₁.gpr]) (by omega_arith)) (hin s₁ (o + 4) m₁.wr (by omega_arith))
    fun s₂ m₂ => ?_
  refine wp_storeS (hea s₂ (o + 8) (by rw [m₂.gpr, m₁.gpr]) (by omega_arith))
    (hin s₂ (o + 8) (by rw [m₂.wr, m₁.wr]) (by omega_arith)) fun s₃ m₃ => ?_
  refine wp_storeS (hea s₃ (o + 12) (by rw [m₃.gpr, m₂.gpr, m₁.gpr]) (by omega_arith))
    (hin s₃ (o + 12) (by rw [m₃.wr, m₂.wr, m₁.wr]) (by omega_arith)) fun s₄ m₄ => WP.block_nil
    ⟨by rw [m₄.gpr, m₃.gpr, m₂.gpr, m₁.gpr], by rw [m₄.rd, m₃.rd, m₂.rd, m₁.rd],
      by rw [m₄.wr, m₃.wr, m₂.wr, m₁.wr], ?_, ?_⟩
  · rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    exact ((((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith)).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))).trans
      ((writeW32_outside _ _ _ (by omega_arith)).mono (by omega_arith) (by omega_arith))
  · have g₃ : s₃.gpr = s.gpr := by rw [m₃.gpr, m₂.gpr, m₁.gpr]
    obtain g₂ : s₂.gpr = s.gpr := by rw [m₂.gpr, m₁.gpr]
    have g₁ : s₁.gpr = s.gpr := m₁.gpr
    intro rd hrd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrd
    rw [m₄.mem, m₃.mem, m₂.mem, m₁.mem]
    rcases hrd with rfl | rfl | rfl | rfl
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32]
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, g₁]
    · rw [Mem.readW_writeW_sep (Offset.sep base (by omega_arith) (by omega_arith) (by omega_arith)) (by decide),
        Mem.readW_writeW_self32, g₂]
    · rw [Mem.readW_writeW_self32, g₃]

/-- The callee-saved registers restored from `o` past the working space,
through `edx`, `edi` last. -/
theorem mulLoads_ok {base : Addr} {s : State} (hs : Scr s base size) {o : Nat} (ho : o + 16 ≤ size)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base (o + rd.2)) 32 = g rd.1) :
    WP isa (.block [.mov .edx (.reg .edi), .mov .ebx (.mem (at_ .edx o)), .mov .esi (.mem (at_ .edx (o + 4))),
        .mov .ebp (.mem (at_ .edx (o + 12))), .mov .edi (.mem (at_ .edx (o + 8)))]) s
      fun s' => s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧
        (∀ r, r ∉ [.ebx, .edx, .esi, .edi, .ebp] → s'.gpr r = s.gpr r) := by
  have hsz : size = 8192 := rfl
  refine wp_movS rfl fun s₇ u₇ _ => ?_
  obtain hs₇ := hs.of_keeps u₇.keeps (by decide)
  obtain hx₇ : s₇.gpr .edx = s₇.gpr .edi := by rw [u₇.gpr, u₇.other _ (by decide)]
  refine wp_movS (restoreLd hs₇ hx₇ (d := o) (by omega_arith)) fun s₈ u₈ _ => ?_
  obtain hs₈ := hs₇.of_keeps u₈.keeps (by decide)
  obtain hx₈ : s₈.gpr .edx = s₈.gpr .edi := by rw [u₈.other _ (by decide), u₈.other _ (by decide), hx₇]
  refine wp_movS (restoreLd hs₈ hx₈ (d := o + 4) (by omega_arith)) fun s₉ u₉ _ => ?_
  obtain hs₉ := hs₈.of_keeps u₉.keeps (by decide)
  obtain hx₉ : s₉.gpr .edx = s₉.gpr .edi := by rw [u₉.other _ (by decide), u₉.other _ (by decide), hx₈]
  refine wp_movS (restoreLd hs₉ hx₉ (d := o + 12) (by omega_arith)) fun s₁₀ u₁₀ _ => ?_
  obtain hs₁₀ := hs₉.of_keeps u₁₀.keeps (by decide)
  obtain hx₁₀ : s₁₀.gpr .edx = s₁₀.gpr .edi := by
    rw [u₁₀.other _ (by decide), u₁₀.other _ (by decide), hx₉]
  refine wp_movS (restoreLd hs₁₀ hx₁₀ (d := o + 8) (by omega_arith)) fun s₁₁ u₁₁ _ => WP.block_nil ?_
  obtain hm₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  obtain hsv' : ∀ rd ∈ Cfg.saved, s₁₀.mem.readW (off base (o + rd.2)) 32 = g rd.1 := fun rd h => by
    rw [hm₁₀]; exact hsv rd h
  refine ⟨by rw [u₁₁.mem, hm₁₀], by rw [u₁₁.rd, u₁₀.rd, u₉.rd, u₈.rd, u₇.rd],
    by rw [u₁₁.wr, u₁₀.wr, u₉.wr, u₈.wr, u₇.wr], fun rd hrd => ?_, fun r hr => ?_⟩
  · simp only [Cfg.saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr,
        show s₇.mem = s₁₀.mem by rw [hm₁₀, u₇.mem]]
      exact hsv' (.ebx, 0) (by simp [Cfg.saved])
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, show s₈.mem = s₁₀.mem by rw [hm₁₀, u₈.mem, u₇.mem]]
      exact hsv' (.esi, 4) (by simp [Cfg.saved])
    · rw [u₁₁.gpr]; exact hsv' (.edi, 8) (by simp [Cfg.saved])
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, show s₉.mem = s₁₀.mem by rw [hm₁₀, u₉.mem, u₈.mem, u₇.mem]]
      exact hsv' (.ebp, 12) (by simp [Cfg.saved])
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hr
    rw [u₁₁.other _ h4, u₁₀.other _ h5, u₉.other _ h3, u₈.other _ h1, u₇.other _ h2]

/-- `vg_<curve>_mul`, from the working space its argument (`Point.ArgP`:
writable, apart from the stack its calls use) and what `mulBody_ok` needs of
it: it returns with the callee-saved registers kept, having changed only
`mulFW`, with `Q 0` accepting what `R` holds. -/
theorem mulFn_ok (hc : CfgOk c) {s : State} {base : Addr} (hp : Point.ArgP s base)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulFn s fun s' => (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Unch base (mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  have hn := hp.nowrap
  obtain hwk := save_le_wk (c := c) h7
  have := wk_own c
  rw [Cfg.mulFn, Cfg.mulSaved]
  -- `eax = ws`, the callee-saved registers saved, `edi = ws`.
  refine WP.seq (wp_ldm (b := .esp) rfl ⟨_, List.mem_append_left _ hp.rd, by
      rw [show addr (s.gpr .esp) (4 + 4 * 0) = argAddr s 0 from rfl]; exact Region.contains_self _ _⟩
    fun s₀ u₀ => ?_)
  have eax₀ : s₀.gpr .eax = arg s 0 := u₀.gpr
  refine WP.block_append (WP.mono (mulSaves_ok (s := s₀) (base := base) (o := c.sl nslots) (by omega_arith)
    (by rw [eax₀]; exact hp.ws) (by rw [eax₀, hp.arg_toNat]; exact hn) (by rw [u₀.wr]; exact hp.wr))
    fun s₁ ⟨g₁, r₁, w₁, O₁, V₁⟩ => ?_)
  refine wp_mov fun s₂ u₂ => WP.block_nil ?_
  have m₂ : s₂.mem = s₁.mem := u₂.mem
  obtain edi₂ : s₂.gpr .edi = arg s 0 := by rw [u₂.gpr, g₁, eax₀]
  obtain esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [u₂.other _ (by decide), g₁, u₀.other _ (by decide)]
  obtain wr₂ : s₂.wr = s.wr := by rw [u₂.wr, w₁, u₀.wr]
  obtain rd₂ : s₂.rd = s.rd := by rw [u₂.rd, r₁, u₀.rd]
  obtain hs₂ : Scr s₂ base size := ⟨by rw [edi₂]; exact hp.ws, by rw [wr₂]; exact hp.wr, hn, by rw [esp₂]; exact hp.stk⟩
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi => by
    show wordsVal s₂.mem _ _ _ = wordsVal s.mem _ _ _
    rw [m₂, show s.mem = s₀.mem from u₀.mem.symm]
    exact O₁.wordsVal (.inl (sl_lt c hi)) (by have := sl_le c h7 hi; omega_arith)
  obtain tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  obtain hstep₂ : Step (ladAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
    rw [e₂ (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) hstep
  obtain hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
      (tmv c.C c.n base s₂ (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  -- The body.
  refine WP.seq (WP.mono (mulBody_ok hc hs₂ (by rw [e₂ (by decide)]; exact hmp)
    (by rw [e₂ (by decide)]; exact hap) (by rw [e₂ (by decide)]; exact hb3) (by rw [e₂ (by decide)]; exact hone)
    (by rw [e₂ (by decide)]; exact hzero) (by rw [e₂ (by decide)]; exact hqx)
    (by rw [e₂ (by decide)]; exact hqy) hstep₂ hO₂) fun s₃ ⟨K₃, U₃, L₃, R₃⟩ => ?_)
  obtain hs₃ := hs₂.of_keeps K₃ (by decide)
  obtain hsv : ∀ rd ∈ Cfg.saved, s₃.mem.readW (off base (c.sl nslots + rd.2)) 32 = s.gpr rd.1 := fun rd hrd => by
    obtain h16 : rd.2 + 4 ≤ 16 := by revert rd; decide
    obtain hne : rd.1 ≠ .eax := by revert rd; decide
    rw [Unch.readW32 U₃ (save_apart h7 (by omega_arith) (by omega_arith)) (by omega_arith), m₂, V₁ rd hrd,
      u₀.other _ hne]
  -- The callee-saved registers restored.
  refine WP.mono (mulLoads_ok hs₃ (o := c.sl nslots) (by omega_arith) hsv) fun s₄ ⟨m₄, r₄, w₄, G₄, k₄⟩ => ?_
  refine ⟨fun r hr => ?_, by rw [r₄, K₃.2.1, rd₂], by rw [w₄, K₃.2.2, wr₂], ?_, by rw [m₄]; exact L₃, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact G₄ (.ebx, 0) (by simp [Cfg.saved])
    · exact G₄ (.esi, 4) (by simp [Cfg.saved])
    · exact G₄ (.edi, 8) (by simp [Cfg.saved])
    · exact G₄ (.ebp, 12) (by simp [Cfg.saved])
    · rw [k₄ _ (by decide), K₃.1 _ (by decide), esp₂]
  · rw [m₄]
    obtain U₁ : Unch base [(c.sl nslots, 16)] s.mem s₂.mem := by rw [m₂, show s.mem = s₀.mem from u₀.mem.symm]; exact O₁.unch
    exact (U₁.trans U₃).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw ⊢
      rcases hw with hw | hw
      · exact .inr hw
      · exact .inl hw
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [m₄]; exact R₃

end VG.Proof.Ecdsa.X86

end

end


/-!
# `[k]P` on x86 (32-bit): the call of `vg_<curve>_mul`, or the ladder inline

`qMul_ok`: `R = [k]P` for the point at `gx`, `gy`, `ONEP` (`Cfg.qMul`), by a
call of `vg_<curve>_mul` if the curve has it (`Cfg.mul`), from `k` at `K`'s
slot, else by the signature's ladder inline (`ladderP`), from the table of
`k`'s bits. For any invariant `Q` of the ladder from that point that accepts
both `R` and `O` (as zero and one hold it), `Q 0` accepts what `R` holds at
the end; only `powClob`, what `ladderP` writes and `genX` change, and the
caller's argument holding the working space (`Point.LadArg`), which the call
reloads `edi` from as `ladderP`'s calls do, is kept. As on PPC64LE
(`Proof/Ecdsa/PPC64LE/LadPow.lean`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `qMul` writes besides `ladderP`: `ACC`, `PT` (`vg_<curve>_mul`'s
copy of `Q`), the table of `k`'s bits and where it keeps the callee-saved
registers. -/
abbrev genX (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 16)]

theorem apart_genX (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hr : i ∉ [ACC, PT]) :
    ∀ w ∈ genX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hr) ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (by have := sl_below_bits c hi 0 0; omega_arith)
  · exact Or.inl (sl_lt c hi)

theorem fixedOk_genX (h7 : c.n < 10) : FixedOk c (genX c) := by
  refine (fixedOk_slW (l := [ACC, PT]) (by decide)).append ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (i := 12) (by decide) 0 0))
  · exact Or.inr (Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _)
      (sl_lt c (i := 12) (j := nslots) (by decide)))))

theorem tbl_apart_genX (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ genX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  have := sl_below_bits c (i := ACC) (by decide) j t
  have := sl_below_bits c (i := PT) (by decide) j t
  have := save_le_wk (c := c) h7
  have := wk_below_bits c j
  have := bitsAt_eq c j
  have := bitsAt_eq c 0
  obtain hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj
  have : (64 * c.n + 4) * 1 ≤ (64 * c.n + 4) * j := Nat.mul_le_mul_left _ hj1
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false, List.mem_append, slW, List.map_cons, List.map_nil] at hw
  rcases hw with (rfl | rfl) | rfl | rfl <;> (dsimp only; omega_arith)

theorem flag_apart_genX (h0 : 0 < c.n) (h7 : c.n < 10) : ∀ w ∈ genX c, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
  intro w hw
  rcases apart_genX h7 (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact .inl (by omega_arith)
  · exact .inr h

/-- Memory that changed only in the 8 bytes below `esp` (a push and a return
address) keeps the working space. -/
theorem unch_of_frame8 {s : State} {base : Addr} (hs : Scr s base 8192) {m m' : Mem}
    (hF : Frame [below (s.gpr .esp) 8] m m') (h28 : 28 ≤ (s.gpr .esp).toNat)
    (hz : (s.gpr .esp).toNat ≤ base.toNat ∨ base.toNat + 8192 + 28 ≤ (s.gpr .esp).toNat) :
    Unch base [Mont.outW] m m' := fun x hx => hF x fun r hr hc => by
  rw [List.mem_singleton.mp hr] at hc
  have := Point.zone8 hs h28 hz hc
  have := hx _ (List.mem_singleton_self _)
  simp only at this
  have := (x - base).isLt
  simp only [ofs] at *
  omega_arith

theorem mulFW_sub (c : Cfg) (gx gy : Nat) :
    ∀ w ∈ mulFW c, w ∈ Point.ladWp (ladAt c gx gy) c.wk ++ genX c := by
  intro w hw
  simp only [mulFW, mulBW, mulBX, List.mem_append, List.mem_singleton] at hw
  simp only [Point.ladWp, List.mem_append, genX, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with (hw | hw | hw) | hw
  · exact .inl (.inl hw)
  · exact .inr (.inl hw)
  · exact .inr (.inr (.inl hw))
  · exact .inr (.inr (.inr hw))

/-- `vg_<curve>_mul` as the call sees it: from a state whose working space
is the argument, writable and the only writable region, with the numbers of
`s₀`'s working space, it changes only `mulFW`, with `Q 0` accepting what `R`
holds. -/
def mulK (c : Cfg) (base : Addr) (s₀ : State) (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) : Contract isa where
  pre u := Point.ArgP u base ∧ u.wr = [⟨base, 8192⟩] ∧
    Region.Disjoint ⟨(u.gpr .esp).setWidth 64, 4⟩ ⟨base, 8192⟩ ∧ Unch base [Mont.outW] s₀.mem u.mem
  post u u' := Unch base (mulFW c) u.mem u'.mem ∧
    (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u'.mem base x c.n < c.C.p) ∧
    Q 0 (tmv c.C c.n base u' (c.sl RX)) (tmv c.C c.n base u' (c.sl RY)) (tmv c.C c.n base u' (c.sl RZ))
  pub _ _ := True

theorem mulK_ok (hc : CfgOk c) (hsp : SpOk c.mulFn 20) {s₀ : State} {base : Addr}
    (hmp : sv c base s₀ MP = c.C.p)
    (hap : sv c base s₀ AP < c.C.p) (hb3 : sv c base s₀ B3P < c.C.p) (hone : sv c base s₀ ONEP < c.C.p)
    (hzero : sv c base s₀ ZERO < c.C.p) (hqx : sv c base s₀ RX < c.C.p) (hqy : sv c base s₀ RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s₀ (sv c base s₀ K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s₀ (c.sl ZERO)) (tmv c.C c.n base s₀ (c.sl ONEP))
      (tmv c.C c.n base s₀ (c.sl ZERO))) (u : State) (hu : (mulK c base s₀ Q).pre u) :
    ∃ tr u', Exec isa c.mulFn u tr u' ∧ abiPreserved u u' ∧ (mulK c base s₀ Q).post u u' := by
  obtain ⟨hpu, hwu, hru, Uu⟩ := hu
  have h7 := hc.n10
  have hsz : size = 8192 := rfl
  obtain sv_u : ∀ {i}, i < 45 → sv c base u i = sv c base s₀ i := fun hi =>
    Uu.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact .inl (by have := sl_le c h7 hi; simp only; omega_arith))
      (by have := sl_le c h7 hi; omega_arith)
  obtain tv : ∀ {i}, i < 45 → tmv c.C c.n base u (c.sl i) = tmv c.C c.n base s₀ (c.sl i) := fun hi => by
    show toM _ _ (sv c base u _) = toM _ _ (sv c base s₀ _); rw [sv_u hi]
  obtain hstepu : Step (ladAt c RX RY) c.C base u (sv c base u K) Q := by
    rw [sv_u (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) hstep
  obtain hOu : Q c.ladderCfg.nbits (tmv c.C c.n base u (c.sl ZERO)) (tmv c.C c.n base u (c.sl ONEP))
      (tmv c.C c.n base u (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  have h20 := hpu.stk.1
  obtain ⟨tr, u', he, ⟨G, -, -, U, L, R⟩, F⟩ := WP.spFrame hsp h20 (mulFn_ok hc hpu
    (by rw [sv_u (by decide)]; exact hmp) (by rw [sv_u (by decide)]; exact hap)
    (by rw [sv_u (by decide)]; exact hb3) (by rw [sv_u (by decide)]; exact hone)
    (by rw [sv_u (by decide)]; exact hzero) (by rw [sv_u (by decide)]; exact hqx)
    (by rw [sv_u (by decide)]; exact hqy) hstepu hOu)
  refine ⟨tr, u', he, ⟨G, ?_⟩, U, L, R⟩
  refine F.readW (r := ⟨(u.gpr .esp).setWidth 64, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hwu] at hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with rfl | rfl
  · exact hru
  · exact (below_disjoint_ret h20).symm

/-- The call of `vg_<curve>_mul` on `Q` at `R`'s first two slots, from the
working space at `edi`, which is then loaded again from the caller's
argument at `[esp + ao]`. -/
theorem mulCall_ok (hc : CfgOk c) (hsp : SpOk c.mulFn 20) {C : Impl.Weierstrass.Mul.Curve} {ao : Nat}
    {s : State} {base : Addr} (hs : Scr s base size) (hA : Point.LadArg s base ao)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c RX RY) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa (.seq (.frame (.push [.edi]) (.call s!"vg_{C.curve}_mul" c.mulFn) (.pop .eax 1))
      (.block [.mov .edi (.mem (at_ .esp ao))])) s fun s' => Keeps powClob s s' ∧
      Unch base (Mont.outW :: mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) ∧
      Point.LadArg s' base ao := by
  have hn := hs.nowrap
  have h28 := hA.s28
  have hz := hA.sz
  obtain hspN := (s.gpr .esp).isLt
  have hedi := hs.edi_toNat
  have hst : stackUse c.mulFn ≤ 20 := hsp.2
  obtain hfit : 4 * [Reg.edi].length + 4 ≤ (s.gpr .esp).toNat := by
    simp only [List.length_cons, List.length_nil]; omega_arith
  -- The callee's view.
  let t := ((pushed [Reg.edi] s).callEntry).withRegions [below (s.gpr .esp) 4] [⟨base, 8192⟩]
  obtain a0 : arg t 0 = s.gpr .edi := callEntry_arg hfit (by decide) (by decide)
  obtain hws : (arg t 0).setWidth 64 = base := by rw [a0]; exact hs.edi
  obtain espT : (t.gpr .esp).toNat = (s.gpr .esp).toNat - 8 := by
    show ((pushed _ s).callEntry.gpr .esp).toNat = _
    rw [callEntry_espNat hfit]; rfl
  obtain argA : argAddr t 0 = (s.gpr .esp - BitVec.ofNat 32 4).setWidth 64 := callEntry_argAddr0 _ _
  obtain argN : (argAddr t 0).toNat = (s.gpr .esp).toNat - 4 := by
    rw [argA, BitVec.toNat_setWidth, sub_toNat (by omega_arith)]
    exact Nat.mod_eq_of_lt (by omega_arith)
  obtain retN : ((t.gpr .esp).setWidth 64).toNat = (s.gpr .esp).toNat - 8 := by
    rw [BitVec.toNat_setWidth, espT]; exact Nat.mod_eq_of_lt (by omega_arith)
  obtain fr : Frame [below (s.gpr .esp) 8] s.mem t.mem := callEntry_frame hfit (rs := [Reg.edi]) (by decide)
  obtain Ut : Unch base [Mont.outW] s.mem t.mem := unch_of_frame8 hs fr h28 hz
  obtain hargT : Point.ArgP t base :=
    ⟨hws, by show _ ∈ [below (s.gpr .esp) 4]; rw [argA]; exact List.mem_singleton_self _,
      List.mem_singleton_self _, hn, ⟨by rw [espT]; omega_arith, by rw [espT]; omega_arith⟩,
      by rw [espT]; omega_arith,
      Region.disjoint_of_le (by simp only; rw [argN]; omega_arith) (by simp only; rw [argN]; omega_arith)
        (by simp only; omega_arith)⟩
  obtain hretT : Region.Disjoint ⟨(t.gpr .esp).setWidth 64, 4⟩ ⟨base, 8192⟩ :=
    Region.disjoint_of_le (by simp only; rw [retN]; omega_arith) (by simp only; rw [retN]; omega_arith)
      (by simp only; omega_arith)
  obtain hpre : CallPre (mulK c base s Q) [.edi] [below (s.gpr .esp) 4] [⟨base, 8192⟩] s := by
    refine ⟨⟨hargT, rfl, hretT, Ut⟩, ?_, ?_⟩
    · refine Covers.append_left (Covers.of_mem fun r hr => ?_) (Covers.of_mem fun r hr => ?_)
      · rw [List.mem_singleton.mp hr]; simp
      · rw [List.mem_singleton.mp hr]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hs.wr)
    · exact Covers.of_mem fun r hr => by rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ hs.wr
  refine WP.seq (WP.callWith (k := mulK c base s Q) (mulK_ok hc hsp hmp hap hb3 hone hzero hqx hqy hstep hO)
    hsp.1 (by decide) (by decide) (by simp only [List.length_cons, List.length_nil]; omega_arith) hpre ?_)
  intro s' rd' wr' cs' F' ⟨s₃, m₃, U₃, L₃, R₃⟩
  obtain F₂ : Frame [⟨base, 8192⟩, below (s.gpr .esp) 28] s.mem s'.mem := by
    have := Frame.below_mono F' (b := 28) (by simp only [List.length_cons, List.length_nil]; omega_arith) h28
    exact this.mono fun r hr => by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
      exact hr
  obtain esp' : s'.gpr .esp = s.gpr .esp := cs' .esp (by decide)
  refine wp_ldm (b := .esp) esp' (by rw [rd', wr']; exact hA.rd) fun s₄ u₄ => WP.block_nil ?_
  obtain hv' : s'.mem.readW (addr (s.gpr .esp) ao) 32 = s.gpr .edi := by
    rw [F₂.readW (r := ⟨addr (s.gpr .esp) ao, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hA.aw
      · exact hA.as) (by decide), hA.val]
  obtain m₄ : s₄.mem = s'.mem := u₄.mem
  obtain U' : Unch base [Mont.outW] s₃.mem s'.mem :=
    unch_of_frame8 hs (Frame.below_mono (wr := []) m₃ (by decide) (by omega_arith)) h28 hz
  have h7 := hc.n10
  obtain sv' : ∀ {i}, i < 45 → sv c base s' i = sv c base s₃ i := fun hi =>
    U'.wordsVal (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact .inl (by have := sl_le c h7 hi; simp only; omega_arith))
      (by have := sl_le c h7 hi; omega_arith)
  obtain eX : wordsVal s'.mem base (c.sl RX) c.n = wordsVal s₃.mem base (c.sl RX) c.n := sv' (by decide)
  obtain eY : wordsVal s'.mem base (c.sl RY) c.n = wordsVal s₃.mem base (c.sl RY) c.n := sv' (by decide)
  obtain eZ : wordsVal s'.mem base (c.sl RZ) c.n = wordsVal s₃.mem base (c.sl RZ) c.n := sv' (by decide)
  obtain edi₄ : s₄.gpr .edi = s.gpr .edi := by rw [u₄.gpr, hv']
  refine ⟨⟨fun r hr => ?_, by rw [u₄.rd, rd'], by rw [u₄.wr, wr']⟩, ?_, ?_, ?_, ?_⟩
  · by_cases h : r = .edi
    · subst h; exact edi₄
    · rw [u₄.other _ h]
      exact cs' r (by revert hr h; cases r <;> decide)
  · rw [m₄]
    exact fun x hx => (U' x fun w hw => hx w (List.mem_append_left _ hw)).trans ((Ut.trans U₃) x hx)
  · rw [m₄]
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [eX]; exact L₃ _ (by simp)
    · rw [eY]; exact L₃ _ (by simp)
    · rw [eZ]; exact L₃ _ (by simp)
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [m₄, eX, eY, eZ]; exact R₃
  · exact hA.keep (by rw [u₄.other _ (by decide), esp']) edi₄ (by rw [u₄.rd, rd']) (by rw [u₄.wr, wr'])
      (by rw [m₄]; exact F₂)

/-- The call's stack: what `vg_<curve>_mul`'s own calls use, below the push
and the return address. -/
theorem mulFn_spOk {gx gy ao : Nat} {C : Impl.Weierstrass.Mul.Curve} (hC : c.mul = some C)
    (h : SpOk (c.qMul gx gy ao) 28) : SpOk c.mulFn 20 := by
  unfold Cfg.qMul at h
  simp only [hC] at h
  refine ⟨fun i hi => h.1 i ?_, ?_⟩
  · simp only [Cfg.mulAt, instrs, List.mem_append, List.mem_cons]
    simp [hi]
  · have := h.2
    simp only [Cfg.mulAt, stackUse, frameBytes, List.length_cons, List.length_nil, Nat.max_le] at this
    omega_using [this]

/-- `R = [k]P` for the point at `gx`, `gy`, `ONEP`: the call of
`vg_<curve>_mul` if the curve has it, from `k` at `K`'s slot, else the ladder
inline, from the table of `k`'s bits. -/
theorem qMul_ok (hc : CfgOk c) {gx gy ao : Nat} (hgx : gx < 45) (hgy : gy < 45) (hg1 : gx ≠ RX)
    (hg2 : gy ≠ RX) (hg3 : gy ≠ RY)
    (hL : LadLay (ladAt c gx gy) size) (hW : LadWk (ladAt c gx gy) c.SP c.C.p size c.wk)
    (hP : 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadPt (ladAt c gx gy))
    (hsp : SpOk (c.qMul gx gy ao) 28)
    {s : State} {base : Addr} (hs : Scr s base size)
    (hA : c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s base ao)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s gx < c.C.p) (hqy : sv c base s gy < c.C.p)
    (hrx : sv c base s RX < c.C.p) (hry : sv c base s RY < c.C.p) (hrz : sv c base s RZ < c.C.p)
    {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (ladAt c gx gy) c.C base s k Q c.qA0)
    (hR : Q (64 * c.n) (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)))
    (hO : Q (64 * c.n) (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)))
    (hk : c.mul.isSome → sv c base s K = k)
    (ht : c.mul = none → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.qMul gx gy ao) s fun s' => Keeps powClob s s' ∧
      Unch base (Point.ladWp (ladAt c gx gy) c.wk ++ genX c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) ∧
      (c.mul.isSome ∨ 3 ≤ c.n ∧ c.n ≤ 6 → Point.LadArg s' base ao) := by
  have h7 := hc.n10
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Cfg.qMul
  split
  · -- The call: `Q` copied to `R`'s first two slots.
    next C hC =>
    obtain hsome : c.mul.isSome := by rw [hC]; rfl
    rw [Cfg.mulAt]
    refine WP.seq ?_
    refine WP.block_append (WP.mono (copySl_ok hc hs (o := RX) (a := gx) (by decide) hgx (Ne.symm hg1))
      fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
    obtain hs₁ := hs.of_keeps k₁ (by decide)
    refine WP.mono (copySl_ok hc hs₁ (o := RY) (a := gy) (by decide) hgy (Ne.symm hg3))
      fun s₂ ⟨x₂, k₂, O₂⟩ => ?_
    obtain hs₂ := hs₁.of_keeps k₂ (by decide)
    obtain K₂ : Keeps [.eax] s s₂ := k₁.trans k₂
    obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
        sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
    obtain e₂ : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c base s₂ i = sv c base s i := fun hi h1 h2 =>
      (o O₂ hi h2).trans (o O₁ hi h1)
    obtain rx₂ : sv c base s₂ RX = sv c base s gx := (o O₂ (by decide) (by decide)).trans x₁
    obtain ry₂ : sv c base s₂ RY = sv c base s gy := x₂.trans (o O₁ hgy hg2)
    obtain U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := by
      have := O₁.unch.trans O₂.unch
      exact this.mono fun w hw => by simpa using hw
    obtain hA₂ : Point.LadArg s₂ base ao := (hA (.inl hsome)).keep (K₂.1 _ (by decide)) (K₂.1 _ (by decide))
      K₂.2.1 K₂.2.2 (frame_of_unch U₂ (slW_le h7 (by decide)) (List.mem_cons_self ..))
    obtain tv : ∀ {i j}, sv c base s₂ i = sv c base s j →
        tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
      show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [h]
    obtain hq : c.qA0 = false := by simp only [Cfg.qA0, hC, Option.isNone_some, Bool.false_and]
    rw [hq] at hstep
    obtain hstep₂ : Step (ladAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
      rw [e₂ (by decide) (by decide) (by decide), hk hsome]
      exact step_congr (L := ladAt c gx gy) (L' := ladAt c RX RY) rfl (tv (e₂ (by decide) (by decide) (by decide)))
        (tv (e₂ (by decide) (by decide) (by decide))) (tv rx₂) (tv ry₂)
        (tv (e₂ (by decide) (by decide) (by decide))) hstep
    obtain hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
        (tmv c.C c.n base s₂ (c.sl ZERO)) := by
      rw [tv (e₂ (i := ZERO) (by decide) (by decide) (by decide)),
        tv (e₂ (i := ONEP) (by decide) (by decide) (by decide))]
      exact hO
    refine WP.mono (mulCall_ok hc (mulFn_spOk hC hsp) (C := C) hs₂ hA₂
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hmp)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hap)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hb3)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hone)
      (by rw [e₂ (by decide) (by decide) (by decide)]; exact hzero)
      (by rw [rx₂]; exact hqx) (by rw [ry₂]; exact hqy) hstep₂ hO₂) fun s' ⟨K', U', L', R', A'⟩ =>
      ⟨(K₂.mono (by decide)).trans K', ?_, L', R', fun _ => A'⟩
    refine (U₂.trans U').mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rw [ladWx_at]
      refine List.mem_append_left _ (List.mem_map.mpr ⟨i, ?_, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with rfl | rfl <;> simp
    rcases List.mem_cons.mp hw with hw | hw
    · rw [hw]
      refine List.mem_append_left _ (List.mem_append_left _ ?_)
      rw [ladWx_at]; simp [wkW]
    · exact mulFW_sub c gx gy w hw
  · -- The ladder inline.
    next hN =>
    obtain hlt : ∀ x ∈ ladR (ladAt c gx gy), wordsVal s.mem base x (ladAt c gx gy).M.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, gx, gy, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c base s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hap
      · exact hb3
      · exact hqx
      · exact hqy
      · exact hone
      · exact hrx
      · exact hry
      · exact hrz
    have hnone : c.mul = none := hN
    refine WP.mono (Point.ladderP_ok (L := ladAt c gx gy) (k := k) hL hW hP hpR hs
      (fun h => hA (.inr h)) (modP_of hc hmp) hlt (fun h => by
        simp only [Cfg.qA0, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.2) hstep hR (ht hnone)) fun s' ⟨K, U, _, L, R, A⟩ =>
      ⟨K, U.mono fun w hw => List.mem_append_left _ hw, L, R, fun h => A (h.resolve_left (by rw [hnone]; decide))⟩

end VG.Proof.Ecdsa.X86

end

end

/-!
# ECDSA on x86 (32-bit): the whole function

`sign_ok`: `Cfg.sign` computes the specification's signature of the hash
with `d` and `k`, for any curve the proof of the code supports (`CfgOk`)
whose group law the proofs support (`Law`), restores the callee-saved
registers and changes memory only in the working space and `out`. Four
stages, each a lemma, as on AArch64 (`Proof/Ecdsa/AArch64/Main.lean`): the
setup and the tables of bits (`stage₁`, in `Stages.lean`), `[k]G` and
`Z^(p-2)` (`stage₂`), `x`, `r`, the checks and `k^(n-2)` (`stage₃`), and
`s`, its check and the result (`stage₄`); `signWith_eq` connects what they
compute to the specification.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg} {A : Args}

/-- The ranges of numbered slots and of the accumulator. -/
abbrev slWk (c : Cfg) (l : List Nat) : List (Nat × Nat) := slW c l ++ wkW c

theorem apart_slWk {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWk c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_wk hi)

theorem tbl_apart_slWk {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWk c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW hl j t) (tbl_apart_wk hj ht)

theorem fixedOk_slWk {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (hn : c.n < 10 := by n10) :
    FixedOk c (slWk c l) :=
  (fixedOk_slW hl).append fixedOk_wk

/-- What the ladder writes: numbered slots, the accumulator and the point
functions' slots. -/
abbrev slWkP (c : Cfg) (l : List Nat) : List (Nat × Nat) := slWk c l ++ Point.ptW c.n

theorem apart_slWkP {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWkP c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slWk hi hl) (apart_ptW hi)

theorem tbl_apart_slWkP {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n)
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWkP c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slWk hl hj ht) (tbl_apart_ptW j t)

theorem fixedOk_slWkP {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (hn : c.n < 10 := by n10) :
    FixedOk c (slWkP c l) :=
  (fixedOk_slWk hl).append fixedOk_ptW

/-- After `[k]G` and `Z^(p-2)`. -/
structure St₂ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  k : sv c base s K = kv c A s₀
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  flag : flagW c base s = BitVec.allOnes 32
  t₂ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  acc_lt : sv c base s ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s ACC) = tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s RZ < c.C.p

/-- What `qMul` writes: the ladder's and `genX`. -/
abbrev slWkG (c : Cfg) (l : List Nat) : List (Nat × Nat) := slWkP c l ++ genX c

theorem apart_slWkG {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hr : i ∉ [ACC, PT])
    (hn : c.n < 10 := by n10) : ∀ w ∈ slWkG c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slWkP hi hl) (apart_genX hn hi hr)

theorem tbl_apart_slWkG {l : List Nat} (hl : ∀ i ∈ l, i < 45) {j t : Nat} (hj : j < 3) (hj0 : j ≠ 0)
    (ht : t < 64 * c.n) (hn : c.n < 10 := by n10) :
    ∀ w ∈ slWkG c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slWkP hl hj ht) (tbl_apart_genX hn hj0 ht)

theorem fixedOk_slWkG {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i) (hn : c.n < 10 := by n10) :
    FixedOk c (slWkG c l) :=
  (fixedOk_slWkP hl).append (fixedOk_genX hn)

/-- The flag word apart from what `qMul` writes. -/
theorem flag_unchG {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slWkG c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega_arith)
  rcases List.mem_append.mp hw with hw | hw
  · rcases apart_slWkP (c := c) (i := FLAG) (by decide) hl h7 w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  · exact flag_apart_genX h0 h7 w hw

/-- `[k]G` (`gen`), then `Z^(p-2)`. -/
theorem stage₂ (hc : CfgOk c) (hC : Law c.C) (hcomb : c.comb = none) {s₀ : State} {base : Addr} {s : State}
    (hS : St₁ c A s₀ base s)
    (hsp₁ : SpOk (c.gen A.ao) c.stk) (hsp₂ : SpOk c.pPow c.stk)
    {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₂ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (c.gen A.ao) (.seq c.pPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hS.fixed
  obtain hkl : kv c A s₀ < 2 ^ (64 * c.n) := hS.k ▸ wordsVal_lt _ _ _ _
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
      (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n)) (G c.C)
    rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
    exact rep_affine' hC _ _
  obtain hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀ >>> (64 * c.n)) (G c.C)) := by
    show Rep c.C (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ)) _
    rw [hS.rx, hS.ry, hS.rz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  obtain hO : Rep c.C (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO)) (mul (kv c A s₀ >>> (64 * c.n)) (G c.C)) := by
    show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)) (toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n))
      (toM _ _ (wordsVal s.mem base (c.sl ZERO) c.n)) _
    rw [F.zero, F.onep, toM_zero, toM_one hpR, shiftRight_eq_zero hkl, mul_zero_pt]
    exact rep_infinity' hC
  obtain hstep := step_rep' (L := c.ladderCfg) (k := kv c A s₀) (a0 := c.qA0) hC hc.onG (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl AP) c.n) = _
      rw [F.ap]; exact toM_cmont hc _)
    (by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl B3P) c.n) = _
      rw [F.b3p]; exact toM_cmont hc _) hG
    (fun h => ⟨by
      simp only [Impl.Ecdsa.X86.Cfg.qA0, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.2.1]; rfl, by
      show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR⟩)
  refine WP.seq (hS.withSp hsp₁ (WP.mono (qMul_ok hc (gx := GX) (gy := GY) (by decide) (by decide)
    (by decide) (by decide) (by decide) (ladLay hc) (ladWk hc) ladPt
    ⟨hsp₁.1, Nat.le_trans hsp₁.2 (Cfg.stk_le c)⟩ hS.scr
    (fun h => hS.arg (Cfg.stk_28q hcomb h)) F.mp
    (lt_of_eq_of_lt F.ap (hmont _)) (lt_of_eq_of_lt F.b3p (hmont _))
    (lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_arith))) (lt_of_eq_of_lt F.zero (by omega_arith))
    (lt_of_eq_of_lt F.gx (hmont _)) (lt_of_eq_of_lt F.gy (hmont _))
    (lt_of_eq_of_lt hS.rx (by omega_arith)) (lt_of_eq_of_lt hS.ry (hmont _)) (lt_of_eq_of_lt hS.rz (by omega_arith))
    hstep hR hO (fun _ => hS.k) (fun _ => hS.t₀)) fun s₅ ⟨K₅, U₅, L₅, R₅, _⟩ f₅ => ?_))
  rw [Nat.shiftRight_zero] at R₅
  rw [Point.ladWp, ladWx_at] at U₅
  obtain hs₅ := hS.scr.of_keeps K₅ (by decide)
  obtain F₅ := F.unch h7 hn (fixedOk_slWkG (l := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2,
    T3, T4, T5, TX, TY, TZ, TMP]) (by decide)) U₅
  obtain k₅ : Keep c s₀ base s₅ := ⟨hs₅, by rw [K₅.1 _ (by decide), hS.esp], by rw [K₅.2.1, hS.rd],
    by rw [K₅.2.2, hS.wr], F₅, f₅, hS.sp_lo⟩
  refine WP.seq (k₅.withSp hsp₂ (WP.mono (pPow_ok hc hs₅ (modP_of hc F₅.mp)
    (L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) F₅.onep
    (fun t ht => by
      show s₅.mem (off base (bitsAt c.n 1 + t)) = _
      rw [tbl_unch U₅ h7 (j := 1) (by decide) ht (tbl_apart_slWkG (by decide) (by decide) (by decide) ht)]
      exact hS.t₁ t ht)
    (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith)) fun s₆ ⟨K₆, U₆, lt₆, v₆⟩ f₆ => h s₆ ?_))
  obtain e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] →
      i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] →
      sv c base s₆ i = sv c base s i := fun hi h₁ h₂ =>
    (sv_unch U₆ h7 hn hi (apart_pwW hi h₁)).trans (sv_unch U₅ h7 hn hi (apart_slWkG hi h₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h₁ ⊢; exact ⟨h₁.1, h₁.2.1⟩)))
  obtain r₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₆ i = sv c base s₅ i := fun hi h₁ =>
    sv_unch U₆ h7 hn hi (apart_pwW hi h₁)
  refine ⟨⟨hs₅.of_keeps K₆ (by decide), by rw [K₆.1 _ (by decide), k₅.esp],
    by rw [K₆.2.1, k₅.rd], by rw [K₆.2.2, k₅.wr], F₅.unch h7 hn fixedOk_pwW U₆, f₆, hS.sp_lo⟩,
    by rw [e₆ (by decide) (by decide) (by decide), hS.k],
    by rw [e₆ (by decide) (by decide) (by decide), hS.d],
    by rw [e₆ (by decide) (by decide) (by decide), hS.e],
    by rw [flagW, flag_unch_pwW U₆ h7 h0 hn, flag_unchG U₅ h7 h0 hn (by decide), ← flagW, hS.flag],
    ?_, ?_, lt₆, ?_, ?_⟩
  · intro t ht
    rw [tbl_unch U₆ h7 (j := 2) (by decide) ht (tbl_apart_pwW (by decide) ht),
      tbl_unch U₅ h7 (j := 2) (by decide) ht (tbl_apart_slWkG (by decide) (by decide) (by decide) ht)]
    exact hS.t₂ t ht
  · show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [r₆ (i := RX) (by decide) (by decide), r₆ (i := RY) (by decide) (by decide),
      r₆ (i := RZ) (by decide) (by decide)]
    exact R₅
  · show _ = toM _ _ (sv c base s₆ RZ) ^ _
    rw [r₆ (i := RZ) (by decide) (by decide)]
    exact v₆
  · rw [r₆ (i := RZ) (by decide) (by decide)]
    exact L₅ (c.sl RZ) (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

/-- After `x`, `r`, the checks and `k^(n-2)`. -/
structure St₃ (c : Cfg) (A : Args) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  d : sv c base s D = dv c A s₀
  e : sv c base s E = ev c A s₀
  rep : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
    (tmv c.C c.n base s (c.sl RZ)) (mul (kv c A s₀) (G c.C))
  x_lt : sv c base s X < c.C.p
  x : Fin.ofNat c.C.p (sv c base s X) =
    tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2)
  rr : sv c base s RR = sv c base s X % c.C.n
  flag : flagW c base s = BitVec.allOnes 32 &&&
    mask32 (0 < dv c A s₀ ∧ dv c A s₀ < c.C.n) &&& mask32 (0 < kv c A s₀ ∧ kv c A s₀ < c.C.n) &&&
    mask32 (sv c base s X % c.C.n ≠ 0)
  acc : toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) = Fin.ofNat c.C.n (kv c A s₀) ^ (c.C.n - 2)

/-- `x`, `r`, `k R mod n` and the checks, then `k^(n-2)`. -/
theorem stage₃ (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (hS : St₂ c A s₀ base s)
    (hsp₁ : SpOk c.middle c.stk) (hsp₂ : SpOk c.nPow c.stk) {rest : Prog isa} {Q : State → Prop} (h : ∀ s', St₃ c A s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq c.middle (.seq c.nPow rest)) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  refine WP.seq (hS.withSp hsp₁ ?_)
  rw [middle_eq]
  refine midOps_ok hc hS.scr (modP_of hc F.mp) (modN_of hc F.mn) hS.acc_lt F.one F.zero F.r2n
    fun s₇ Mp => ?_
  obtain F₇ := F.unch h7 hn (fixedOk_slWk (l := [XM, X, RR, KM, TMP]) (by decide)) Mp.unch
  refine WP.mono (checks_ok hc Mp.scr F₇.mn) fun s₈ ⟨f₈, k₈, O₈⟩ w₈ => ?_
  obtain hs₈ := Mp.scr.of_keeps k₈ (by decide)
  obtain F₈ := F₇.unch h7 hn fixedOk_flag O₈.unch
  obtain e₈ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₈ i = sv c base s₇ i := fun hi hf =>
    sv_flag O₈ h0 h7 hn hi hf
  obtain e₇ : ∀ {i}, i < 45 → i ∉ [XM, X, RR, KM, TMP] → sv c base s₇ i = sv c base s i := fun hi hl =>
    sv_unch Mp.unch h7 hn hi (apart_slWk hi hl)
  obtain K₈ : Keep c s₀ base s₈ := ⟨hs₈, by rw [k₈.1 _ (by decide), Mp.gpr _ (by decide), hS.esp],
    by rw [k₈.2.1, Mp.rd, hS.rd], by rw [k₈.2.2, Mp.wr, hS.wr], F₈, w₈, hS.sp_lo⟩
  refine WP.seq (K₈.withSp hsp₂ (WP.mono (nPow_ok hc hs₈
    (modN_of hc F₈.mn) (lt_of_eq_of_lt (e₈ (i := KM) (by decide) (by decide)) Mp.km_lt) F₈.onen
    (fun t ht => by
      show s₈.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch O₈.unch h7 (j := 2) (by decide) ht (tbl_apart_flag h0 2 t),
        tbl_unch Mp.unch h7 (j := 2) (by decide) ht (tbl_apart_slWk (by decide) (by decide) ht)]
      exact hS.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith)) fun s₉ ⟨K₉, U₉, lt₉, v₉⟩ w₉ => h s₉ ?_))
  obtain e₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₉ i = sv c base s₈ i := fun hi hl =>
    sv_unch U₉ h7 hn hi (apart_pwW hi hl)
  -- The slots `middle` and the power do not write.
  obtain a₉ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → i ≠ FLAG → i ∉ [XM, X, RR, KM, TMP] →
      sv c base s₉ i = sv c base s i := fun hi h₁ h₂ h₃ =>
    ((e₉ hi h₁).trans (e₈ hi h₂)).trans (e₇ hi h₃)
  obtain x₉ : sv c base s₉ X = sv c base s₇ X :=
    (e₉ (i := X) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  obtain rr₉ : sv c base s₉ RR = sv c base s₇ RR :=
    (e₉ (i := RR) (by decide) (by decide)).trans (e₈ (by decide) (by decide))
  obtain tR : ∀ i ∈ [RX, RY, RZ], tmv c.C c.n base s₉ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi
    show toM _ _ (sv c base s₉ i) = toM _ _ (sv c base s i)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rw [a₉ (by decide) (by decide) (by decide) (by decide)]
  refine ⟨⟨hs₈.of_keeps K₉ (by decide), by rw [K₉.1 _ (by decide), K₈.esp], by rw [K₉.2.1, K₈.rd],
    by rw [K₉.2.2, K₈.wr], F₈.unch h7 hn fixedOk_pwW U₉, w₉, hS.sp_lo⟩,
    by rw [a₉ (i := D) (by decide) (by decide) (by decide) (by decide), hS.d],
    by rw [a₉ (i := E) (by decide) (by decide) (by decide) (by decide), hS.e],
    by rw [tR RX (by simp), tR RY (by simp), tR RZ (by simp)]; exact hS.rep,
    by rw [x₉]; exact Mp.x_lt,
    by rw [x₉, Mp.x, tR RX (by simp), tR RZ (by simp), hS.acc],
    by rw [rr₉, x₉]; exact Mp.rr, ?_, ?_⟩
  · rw [flagW, flag_unch_pwW U₉ h7 h0 hn, ← flagW, f₈, flagW, flag_unch Mp.unch h7 h0 hn (by decide),
      ← flagW, hS.flag, e₇ (i := D) (by decide) (by decide), e₇ (i := K) (by decide) (by decide), hS.d, hS.k,
      Mp.rr, x₉]
  · refine v₉.trans ?_
    show toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ KM) ^ _ = _
    rw [e₈ (i := KM) (by decide) (by decide), Mp.km, hS.k]

/-- The result the contract asks for: the specification's signature of the
hash with `d` and `k`, big-endian, and `1`, or zeros and `0`. -/
def SignPost (c : Cfg) (s₀ s' : State) : Prop :=
  match Spec.Ecdsa.signWith c.C (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 1) c.C.len))
      (Spec.Ecdsa.hashToInt c.C (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) c.C.len))
      (ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 3) c.C.len)) with
  | some rs => s'.gpr .eax = 1 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (2 * c.C.len) = Spec.Ecdsa.encode c.C rs
  | none => s'.gpr .eax = 0 ∧
      Spec.Ecdsa.bytesAt s'.mem (ptr s₀ 0) (2 * c.C.len) = List.replicate (2 * c.C.len) 0

/-- What the ABI asks for, but the return address: the callee-saved
registers restored, `esp` kept; and memory changed only in the writable
regions and the stack below `esp` that the calls use. -/
structure SignKeep (c : Cfg) (s₀ s' : State) : Prop where
  saved : ∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1
  esp : s'.gpr .esp = s₀.gpr .esp
  frame : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s'.mem

/-- Memory the code does not write: a region apart from the writable regions
and the stack the calls use. -/
theorem Pre.frame_readW {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {m : Mem}
    (hf : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem m) {a : Addr} (hb : (⟨a, 4⟩ : Region).Disjoint (outR c s₀))
    (hs : (⟨a, 4⟩ : Region).Disjoint (scR s₀)) (hl : (⟨a, 4⟩ : Region).Disjoint (below (s₀.gpr .esp) c.stk)) :
    m.readW a 32 = s₀.mem.readW a 32 := by
  refine hf.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  rw [hp.wr] at hr
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact hb
  · exact hs
  · exact hl

/-- The return address is kept. -/
theorem SignKeep.ret {s₀ s' : State} {extra : List Region} (hp : Pre c s₀ extra) (K : SignKeep c s₀ s') :
    s'.mem.readW ((s₀.gpr .esp).setWidth 64) 32 = s₀.mem.readW ((s₀.gpr .esp).setWidth 64) 32 :=
  hp.frame_readW K.frame hp.ret_out hp.ret_sc (below_disjoint_ret hp.sp_lo).symm

/-- The calls of `scalar`, before its checks. -/
abbrev scalarOps (c : Cfg) : Prog isa :=
  [Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N), Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N), Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM),
    Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM), Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT)].foldr
    .seq (Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))

theorem scalar_split (c : Cfg) : c.scalar =
    [Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N), Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N),
    Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N), Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM),
    Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM), Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT)].foldr
    .seq (.seq (Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))
      (.block (c.checkNonzero (c.sl SS) ++ c.finish))) := rfl

/-- `s`, its check, and the result. -/
theorem stage₄ (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {extra : List Region} (hp : Pre c s₀ extra) {base : Addr} (hb : base = ptr s₀ 4)
    {s : State} (hS : St₃ c .sign s₀ base s) (hsp : SpOk (scalarOps c) c.stk) :
    WP isa c.scalar s fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hS.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have F := hS.fixed
  rw [scalar_split, WP.split]
  refine WP.seq (hS.withSp hsp ?_)
  rw [← WP.seq_nil, ← WP.split]
  refine scalarIn_ok hc hS.scr (modN_of hc F.mn) F.r2n
    fun s₁₀ hs₁₀ hM₁₀ g₁₀ rd₁₀ wr₁₀ U₁₀ _ dm em trm tdm tem => ?_
  obtain F₁₀ := F.unch h7 hn (fixedOk_slWk (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₀
  refine scalarOut_ok hc hs₁₀ hM₁₀ F₁₀.one dm em
    fun s₁₁ hs₁₁ g₁₁ rd₁₁ wr₁₁ U₁₁ ss_lt ss => WP.block_nil fun w₁₁ => ?_
  obtain hF := sl_le c h7 (i := FLAG) (by decide)
  refine WP.block_append (WP.mono (checkNonzero_ok c hs₁₁ h0 (sl_le c h7 (i := SS) (by decide)) (by omega_arith))
    fun s₁₂ ⟨f₁₂, k₁₂, O₁₂⟩ => ?_)
  obtain hs₁₂ := hs₁₁.of_keeps k₁₂ (by decide)
  obtain F₁₂ := (F₁₀.unch h7 hn (fixedOk_slWk (l := [RM, DM, EM, TT, SM, SS, TMP]) (by decide)) U₁₁).unch
    h7 hn fixedOk_flag O₁₂.unch
  obtain hsc : (⟨base, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [hp.wr, hb]; simp)
  obtain W₁₂ : Frame (s₀.wr ++ [below (s₀.gpr .esp) c.stk]) s₀.mem s₁₂.mem :=
    w₁₁.trans (frame_of_unch O₁₂.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; dsimp only; omega_arith) hsc)
  obtain acc₁₀ : sv c base s₁₀ ACC = sv c base s ACC :=
    sv_unch U₁₀ h7 hn (by decide) (apart_slWk (by decide) (by decide))
  obtain rr₁₂ : sv c base s₁₂ RR = sv c base s RR :=
    ((sv_flag O₁₂ h0 h7 hn (i := RR) (by decide) (by decide)).trans
      (sv_unch U₁₁ h7 hn (by decide) (apart_slWk (by decide) (by decide)))).trans
      (sv_unch U₁₀ h7 hn (by decide) (apart_slWk (by decide) (by decide)))
  obtain ss₁₂ : sv c base s₁₂ SS = sv c base s₁₁ SS := sv_flag O₁₂ h0 h7 hn (by decide) (by decide)
  -- The flag.
  obtain hflag : flagW c base s₁₂ =
      mask32 (decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true) := by
    rw [f₁₂, flagW, flag_unch U₁₁ h7 h0 hn (by decide), flag_unch U₁₀ h7 h0 hn (by decide), ← flagW, hS.flag,
      BitVec.allOnes_and, mask32_and, mask32_and, mask32_and]
    simp only [mask32, decide_eq_true_eq]
  obtain hesp : s₁₂.gpr .esp = s₀.gpr .esp := by
    rw [k₁₂.1 _ (by decide), g₁₁ _ (by decide), g₁₀ _ (by decide), hS.esp]
  obtain hrw : s₁₂.rd ++ s₁₂.wr = s₀.rd ++ s₀.wr := by
    rw [k₁₂.2.1, k₁₂.2.2, rd₁₁, wr₁₁, rd₁₀, wr₁₀, hS.rd, hS.wr]
  obtain hout := argLoad_frame (i := 0) ⟨argsR s₀, by rw [hp.rd]; simp, arg_contains hp.sp_fit (by decide)⟩
    (by
      rw [hp.wr]
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact hp.args_out.sub_left (arg_sub hp.sp_fit (by decide))
      · exact hp.args_sc.sub_left (arg_sub hp.sp_fit (by decide))
      · exact (below_disjoint_args hp.sp_lo (by have := hp.sp_fit; omega_arith) (by decide)).symm)
    hesp hrw W₁₂
  obtain hw : (⟨(arg s₀ 0).setWidth 64, 2 * c.C.len⟩ : Region) ∈ s₁₂.wr := by
    rw [k₁₂.2.2, wr₁₁, wr₁₀, hS.wr, hp.wr]; simp
  refine WP.mono (finish_ok hc hs₁₂ hout hp.out_fit hw (hb ▸ hp.out_sc) F₁₂.saved _ hflag)
    fun s' ⟨bytes, ret, saved, others, Oout⟩ => ⟨⟨saved, by rw [others _ (by decide), hesp],
      W₁₂.trans (frame_of_outside Oout (List.mem_append_left _ (by rw [hp.wr]; simp)))⟩, ?_⟩
  -- The specification.
  obtain hsig := signWith_eq hC (C := c.C) (d := dv c .sign s₀) (e := ev c .sign s₀) (k := kv c .sign s₀) hS.rep hS.x_lt hS.x
    (s := wordsVal s₁₁.mem base (c.sl SS) c.n) ss_lt (by
      rw [ss, trm, tdm, tem, acc₁₀, hS.acc, hS.rr, hS.d, hS.e, Lean.Grind.AddCommMonoid.add_comm])
  unfold SignPost
  obtain he : ofBytes (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) c.C.len) >>> c.sh = ev c .sign s₀ :=
    congrArg (_ >>> ·) (shAt_self c E).symm
  rw [← dv_eq (A := .sign) (shAt_E_D c), ← kv_eq (A := .sign) (shAt_E_K c), hashToInt_eq c, he, hsig]
  rw [ss₁₂, rr₁₂, hS.rr] at bytes
  by_cases hP : 1 ≤ dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n ∧ 1 ≤ kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n ∧
      sv c base s X % c.C.n ≠ 0 ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = true := by
      simp only [decide_eq_true_eq]; omega_arith
    rw [ite_eq_left_of_eq_true _ _ (eq_true hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd, ite_eq_left_of_eq_true _ _ (eq_true rfl), Spec.Ecdsa.encode]
  · have hd : decide ((((0 < dv c .sign s₀ ∧ dv c .sign s₀ < c.C.n) ∧ (0 < kv c .sign s₀ ∧ kv c .sign s₀ < c.C.n)) ∧
        sv c base s X % c.C.n ≠ 0) ∧ wordsVal s₁₁.mem base (c.sl SS) c.n ≠ 0) = false := by
      simp only [decide_eq_false_iff_not]; omega_arith
    rw [ite_eq_right_of_eq_false _ _ (eq_false hP)]
    refine ⟨by rw [ret, hd]; rfl, ?_⟩
    rw [bytes, hd]; rfl

theorem sign_eq (c : Cfg) : c.sign = .seq (.block c.setup) (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n)) (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n))
    (.seq (c.gen Args.sign.ao) (.seq c.pPow (.seq c.middle
      (.seq c.nPow c.scalar))))))) := rfl

/-- The stack the parts of `sign` use: no write of `esp`, and at most
`c.stk` bytes below it. -/
structure SignSp (c : Cfg) : Prop where
  ladder : SpOk (c.gen Args.sign.ao) c.stk
  pPow : SpOk c.pPow c.stk
  middle : SpOk c.middle c.stk
  nPow : SpOk c.nPow c.stk
  scalar : SpOk (scalarOps c) c.stk

/-- `SignSp` from the whole code's. -/
theorem SignSp.of (h : SpOk c.sign c.stk) : SignSp c := by
  rw [sign_eq] at h
  have h₁ := h.right.right.right.right
  have h₂ := h₁.right.right.right
  refine ⟨h₁.left, h₁.right.left, h₁.right.right.left, h₂.left, ?_⟩
  have h₃ := h₂.right
  rw [scalar_split] at h₃
  exact (SpOk.split _ _ _ h₃).1

/-- `vg_ecdsa_<curve>_sign` computes the specification's signature, restores
the callee-saved registers and changes only the working space and `out`. -/
theorem sign_ok (hc : CfgOk c) (hC : Law c.C) (hcomb : c.comb = none) (hsp : SpOk c.sign c.stk) {s₀ : State}
    (hp : Pre c s₀) :
    WP isa c.sign s₀ fun s' => SignKeep c s₀ s' ∧ SignPost c s₀ s' := by
  obtain H := SignSp.of hsp
  rw [sign_eq]
  exact stage₁ hc hp.setup fun _ S₁ => stage₂ hc hC hcomb S₁ H.ladder H.pPow fun _ S₂ =>
    stage₃ hc S₂ H.middle H.nPow fun _ S₃ => stage₄ hc hC hp rfl S₃ H.scalar

end VG.Proof.Ecdsa.X86
