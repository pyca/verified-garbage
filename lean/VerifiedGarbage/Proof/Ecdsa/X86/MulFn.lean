module

import VerifiedGarbage.Proof.Ecdsa.X86.Stages
public import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Weierstrass.X86.Bits
import VerifiedGarbage.Proof.Weierstrass.X86.Copy
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86.Instr
import VerifiedGarbage.Proof.Ecdsa.X86.Finish
public import VerifiedGarbage.Proof.Weierstrass.X86.PointCall
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
public import VerifiedGarbage.Proof.Weierstrass.X86.Ladder
public import VerifiedGarbage.Proof.Weierstrass.X86.LadderP

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
(`Proof/Ecdsa/PPC64LE/MulFn.lean`).
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
  refine WP.mono (copy_ok (2 * c.n) hs (by omega) (by omega) (by omega)) fun s' ⟨e, k, O⟩ => ⟨?_, k, ?_⟩
  · show wordsVal _ _ _ _ = wordsVal _ _ _ _
    rw [wordsVal_eq_val32, wordsVal_eq_val32, e]
  · rw [show 8 * c.n = 4 * (2 * c.n) by omega]; exact O

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
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
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
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (sl_le c h7 (i := K) (by decide)) (bitsAt_le c h7 (j := 0) (by decide))
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0; omega_arith))) fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  have e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    sv_unch O₁.unch h7 hn hi (apart_tbl hi 0)
  -- The copies.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := ACC) (a := RX) (by decide) (by decide) (by decide))
    fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := PT) (a := RY) (by decide) (by decide) (by decide))
    fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₃ (o := RX) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  have hs₄ := hs₃.of_keeps k₄ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₄ (o := RY) (a := ONEP) (by decide) (by decide) (by decide))
    fun s₅ ⟨x₅, k₅, O₅⟩ => ?_)
  have hs₅ := hs₄.of_keeps k₅ (by decide)
  refine WP.mono (copySl_ok hc hs₅ (o := RZ) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨x₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keeps k₆ (by decide)
  have K₁₆ : Keeps powClob s s₆ :=
    (K₁.mono (by decide)).trans ((((k₂.trans k₃).trans k₄).trans k₅).trans k₆ |>.mono (by decide))
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_outside h7 O hi hij
  have e₆ : ∀ {i}, i < 45 → i ∉ [ACC, PT, RX, RY, RZ] → sv c base s₆ i = sv c base s i := fun hi hl => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    rw [o O₆ hi hl.2.2.2.2, o O₅ hi hl.2.2.2.1, o O₄ hi hl.2.2.1, o O₃ hi hl.2.1, o O₂ hi hl.1, e₁ hi]
  have acc₆ : sv c base s₆ ACC = sv c base s RX := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), x₂, e₁ (by decide)]
  have pt₆ : sv c base s₆ PT = sv c base s RY := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), x₃,
      o O₂ (by decide) (by decide), e₁ (by decide)]
  have rx₆ : sv c base s₆ RX = sv c base s ZERO := by
    rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), x₄, o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  have ry₆ : sv c base s₆ RY = sv c base s ONEP := by
    rw [o O₆ (by decide) (by decide), x₅, o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  have rz₆ : sv c base s₆ RZ = sv c base s ZERO := by
    rw [x₆, o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), o O₃ (by decide) (by decide),
      o O₂ (by decide) (by decide), e₁ (by decide)]
  have U₁₆ : Unch base (mulBX c ++ slW c [RX, RY, RZ]) s.mem s₆.mem := by
    have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    refine this.mono fun w hw => ?_
    simp only [slW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.map_cons,
      List.map_nil] at hw ⊢
    rcases hw with h | h | h | h | h | h <;> simp only [h, true_or, or_true]
  have T₆ : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    have U : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem := by
      have := O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch)))
      exact this.mono fun w hw => by simpa using hw
    rw [tbl_unch U h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t), T₁ t ht]
  have tv : ∀ {i j : Nat}, sv c base s₆ i = sv c base s j →
      tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
    show toM _ _ (sv c base s₆ _) = toM _ _ (sv c base s _); rw [h]
  have hstep₆ : Step c.mulLadder c.C base s₆ (sv c base s K) Q :=
    step_congr (L := ladAt c RX RY) (L' := c.mulLadder) rfl (tv (e₆ (by decide) (by decide))) (tv (e₆ (by decide) (by decide)))
      (tv acc₆) (tv pt₆) (tv (e₆ (by decide) (by decide))) hstep
  have hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.mulLadder.M.n < c.C.p := by
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
  have hR : Q c.mulLadder.nbits (tmv c.C c.n base s₆ c.mulLadder.R.x)
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
    have hi' : i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
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
  have hwk := save_le_wk (c := c) h7
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
  have hea : ∀ (t : State) (d : Nat), t.gpr .eax = s.gpr .eax → d < size → t.ea (at_ .eax d) = off base d :=
    fun t d ht hd => by
      show addr (t.gpr .eax) d = _
      rw [ht, addr_eq (by omega_arith), hb]
  have hin : ∀ (t : State) (d : Nat), t.wr = s.wr → d + 4 ≤ size → InRegions t.wr (off base d) 4 :=
    fun t d ht hd => by rw [ht]; exact ⟨_, hw, Offset.contains_base base (by omega_arith) (by omega_arith)⟩
  have hbn : base.toNat + size ≤ 2 ^ 32 := by
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
    have g₂ : s₂.gpr = s.gpr := by rw [m₂.gpr, m₁.gpr]
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
  have hs₇ := hs.of_keeps u₇.keeps (by decide)
  have hx₇ : s₇.gpr .edx = s₇.gpr .edi := by rw [u₇.gpr, u₇.other _ (by decide)]
  refine wp_movS (restoreLd hs₇ hx₇ (d := o) (by omega_arith)) fun s₈ u₈ _ => ?_
  have hs₈ := hs₇.of_keeps u₈.keeps (by decide)
  have hx₈ : s₈.gpr .edx = s₈.gpr .edi := by rw [u₈.other _ (by decide), u₈.other _ (by decide), hx₇]
  refine wp_movS (restoreLd hs₈ hx₈ (d := o + 4) (by omega_arith)) fun s₉ u₉ _ => ?_
  have hs₉ := hs₈.of_keeps u₉.keeps (by decide)
  have hx₉ : s₉.gpr .edx = s₉.gpr .edi := by rw [u₉.other _ (by decide), u₉.other _ (by decide), hx₈]
  refine wp_movS (restoreLd hs₉ hx₉ (d := o + 12) (by omega_arith)) fun s₁₀ u₁₀ _ => ?_
  have hs₁₀ := hs₉.of_keeps u₁₀.keeps (by decide)
  have hx₁₀ : s₁₀.gpr .edx = s₁₀.gpr .edi := by
    rw [u₁₀.other _ (by decide), u₁₀.other _ (by decide), hx₉]
  refine wp_movS (restoreLd hs₁₀ hx₁₀ (d := o + 8) (by omega_arith)) fun s₁₁ u₁₁ _ => WP.block_nil ?_
  have hm₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem]
  have hsv' : ∀ rd ∈ Cfg.saved, s₁₀.mem.readW (off base (o + rd.2)) 32 = g rd.1 := fun rd h => by
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
  have hwk := save_le_wk (c := c) h7
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
  have edi₂ : s₂.gpr .edi = arg s 0 := by rw [u₂.gpr, g₁, eax₀]
  have esp₂ : s₂.gpr .esp = s.gpr .esp := by rw [u₂.other _ (by decide), g₁, u₀.other _ (by decide)]
  have wr₂ : s₂.wr = s.wr := by rw [u₂.wr, w₁, u₀.wr]
  have rd₂ : s₂.rd = s.rd := by rw [u₂.rd, r₁, u₀.rd]
  have hs₂ : Scr s₂ base size := ⟨by rw [edi₂]; exact hp.ws, by rw [wr₂]; exact hp.wr, hn, by rw [esp₂]; exact hp.stk⟩
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi => by
    show wordsVal s₂.mem _ _ _ = wordsVal s.mem _ _ _
    rw [m₂, show s.mem = s₀.mem from u₀.mem.symm]
    exact O₁.wordsVal (.inl (sl_lt c hi)) (by have := sl_le c h7 hi; omega_arith)
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hstep₂ : Step (ladAt c RX RY) c.C base s₂ (sv c base s₂ K) Q := by
    rw [e₂ (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide)) hstep
  have hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
      (tmv c.C c.n base s₂ (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  -- The body.
  refine WP.seq (WP.mono (mulBody_ok hc hs₂ (by rw [e₂ (by decide)]; exact hmp)
    (by rw [e₂ (by decide)]; exact hap) (by rw [e₂ (by decide)]; exact hb3) (by rw [e₂ (by decide)]; exact hone)
    (by rw [e₂ (by decide)]; exact hzero) (by rw [e₂ (by decide)]; exact hqx)
    (by rw [e₂ (by decide)]; exact hqy) hstep₂ hO₂) fun s₃ ⟨K₃, U₃, L₃, R₃⟩ => ?_)
  have hs₃ := hs₂.of_keeps K₃ (by decide)
  have hsv : ∀ rd ∈ Cfg.saved, s₃.mem.readW (off base (c.sl nslots + rd.2)) 32 = s.gpr rd.1 := fun rd hrd => by
    have h16 : rd.2 + 4 ≤ 16 := by revert rd; decide
    have hne : rd.1 ≠ .eax := by revert rd; decide
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
    have U₁ : Unch base [(c.sl nslots, 16)] s.mem s₂.mem := by rw [m₂, show s.mem = s₀.mem from u₀.mem.symm]; exact O₁.unch
    exact (U₁.trans U₃).mono fun w hw => by
      simp only [List.mem_append, List.mem_singleton] at hw ⊢
      rcases hw with hw | hw
      · exact .inr hw
      · exact .inl hw
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [m₄]; exact R₃

end VG.Proof.Ecdsa.X86
