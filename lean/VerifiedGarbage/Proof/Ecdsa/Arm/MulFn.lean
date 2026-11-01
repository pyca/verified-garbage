module

import VerifiedGarbage.Proof.Ecdsa.Arm.Stages
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.Proof.Ecdsa.Arm.Fixed
public import VerifiedGarbage.Proof.Ecdsa.Arm.Layout
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder

/-!
# `vg_<curve>_mul` on 32-bit ARM: correctness

`mulBody` (`Impl/Ecdsa/Arm.lean`) makes the table of the bits of the number
at `K`'s slot, copies `Q` from `R`'s first two slots to `ACC` and `PT`, sets
`R = O` from zero and one, and runs the ladder of `ladderP` from the point
at `ACC`, `PT`, `ONEP` (`mulLadder`). For any invariant `Q` of the ladder
from the point at `RX`, `RY`, `ONEP` (`Step` of `rLadder`, which the copies
carry to `mulLadder`'s point) that accepts `O`, `Q 0` accepts what `R` holds
at the end, and the body writes only what the ladder writes, `ACC`, `PT`
and the table of bits (`mulBody_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest)

variable {c : Cfg}

/-! ## The ladder's layout -/

/-- The ladder from the point at `px`, `py`, `ONEP`: the one whose invariants
the caller of `mulAt` states. -/
abbrev pLadder (c : Cfg) (px py : Nat) : LadderCfg := { c.ladderCfg with G := c.pt px py ONEP }


/-- The ladder from the point at `RX`, `RY`, `ONEP`: the one whose
invariants a caller states, which `mulBody`'s copies carry to `mulLadder`. -/
abbrev rLadder (c : Cfg) : LadderCfg := { c.ladderCfg with G := c.pt RX RY ONEP }

/-- What the point's slots must be for the ladder from them: numbered slots,
neither the modulus's nor the temporary area, and none the ladder writes. -/
def PtSlots (px py : Nat) : Prop :=
  ∀ i ∈ [px, py], i < 45 ∧ i ≠ MP ∧ i ≠ TMP ∧ i ∉ [T0, T1, T2, T3, T4, T5, TX, TY, TZ] ∧
    i ∉ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ]

instance (px py : Nat) : Decidable (PtSlots px py) := by unfold PtSlots; infer_instance

theorem pLadSlots_eq (c : Cfg) (px py : Nat) : ladSlots (pLadder c px py) = [AP, B3P, px, py, ONEP, RX, RY, RZ,
    T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ].map c.sl := rfl

/-- What every slot of the ladder's satisfies, given `PtSlots`. -/
theorem ptSlots_all {px py : Nat} (hp : PtSlots px py) {P : Nat → Prop}
    (hc : ∀ i ∈ [AP, B3P, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ], P i)
    (hpq : ∀ i ∈ [px, py], P i) :
    ∀ i ∈ [AP, B3P, px, py, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ], P i := by
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    subst h <;> first | exact hc _ (by decide) | exact hpq _ (by simp)

theorem pLadLay (hc : CfgOk c) {px py : Nat} (hp : PtSlots px py) : LadLay (pLadder c px py) size 8192 := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, px, py, ONEP]) rfl rfl (by decide) ?_, ?_,
    ⟨fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 8 * c.C.len by have := hc.len8; omega_arith,
      show 8 * c.C.len < 2 ^ 16 by have := hc.len_hi; omega_arith⟩,
    (by have := bitsAt_le c h7 (j := 0) (by decide); have := hc.len_hi;
        change bitsAt c.n 0 + 8 * c.C.len ≤ 8192; omega_arith), ?_⟩
  · exact lay_map hc rfl rfl rfl (ptSlots_all hp (by decide) fun i hi => ⟨(hp i hi).1, (hp i hi).2.1, (hp i hi).2.2.1⟩)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h | h | h | h <;> subst h <;>
      first | decide | exact (hp _ (by simp)).2.2.2.1
  · refine map_sl_disj hn (l₁ := [AP, B3P, px, py, ONEP])
      (l₂ := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ]) ?_
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with h | h | h | h | h <;> subst h <;>
      first | decide | exact (hp _ (by simp)).2.2.2.2
  · exact map_sl_disj hn (l₁ := [RX, RY, RZ]) (l₂ := [DX, DY, DZ, TX, TY, TZ]) (by decide)
  · intro w hw
    simp only [ladW, List.mem_append, List.mem_map, List.mem_singleton] at hw
    rcases hw with ⟨y, hy, rfl⟩ | rfl
    · have hy' : y ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ].map c.sl := hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy'
      have hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
          TY, TZ], i < 45 := by decide
      exact Or.inr (sl_below_bits c hc.n10 (hl i hi) 0 0)
    · exact Or.inr (sl_below_bits c hc.n10 (i := TMP) (by decide) 0 0)

theorem pLadWk (hc : CfgOk c) {px py : Nat} (hp : PtSlots px py) : LadWk (pLadder c px py) size c.wk where
  le := wk_le c hc.n10 rfl
  sl := by
    rw [pLadSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_below_wk c hc.n10 (ptSlots_all hp (P := (· < 45)) (by decide) (fun i hi => (hp i hi).1) i hi)
  mo := sl_below_wk c hc.n10 (i := MP) (by decide)
  tmp := sl_below_wk c hc.n10 (i := TMP) (by decide)
  bits := wk_below_bits c hc.n10 rfl 0

theorem pLadPt {px py : Nat} (hp : PtSlots px py) (h6 : c.n ≤ 6) :
    VG.Proof.Weierstrass.Arm.Point.LadPt (pLadder c px py) where
  sl := by
    rw [pLadSlots_eq]
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact sl_below_pt h6 (ptSlots_all hp (P := (· < 45)) (by decide) (fun i hi => (hp i hi).1) i hi)
  mo := sl_below_pt h6 (i := MP) (by decide)

theorem mulLadLay (hc : CfgOk c) : LadLay c.mulLadder size 8192 := pLadLay (px := ACC) (py := PT) hc (by decide)
theorem mulLadWk (hc : CfgOk c) : LadWk c.mulLadder size c.wk := pLadWk (px := ACC) (py := PT) hc (by decide)
theorem mulLadPt (h6 : c.n ≤ 6) : VG.Proof.Weierstrass.Arm.Point.LadPt c.mulLadder :=
  pLadPt (px := ACC) (py := PT) (by decide) h6

/-- The ladder writes what the signature's does. -/
theorem mulLadWp_eq (c : Cfg) :
    VG.Proof.Weierstrass.Arm.Point.ladWp c.mulLadder c.wk = VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk :=
  rfl

/-! ## The body -/

/-- What `mulBody` writes besides the ladder: `ACC`, `PT` and the table of
the bits of `k`. -/
abbrev mulBX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n)]

/-- What `mulBody` writes. -/
abbrev mulBW (c : Cfg) : List (Nat × Nat) :=
  VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ mulBX c

/-- `Step` depends only on what the slots of `a`, `3b` and the point hold. -/
theorem step_congr {L L' : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hb : L'.nbits = L.nbits)
    (ha : tmv C L'.M.n base s' L'.S.a = tmv C L.M.n base s L.S.a)
    (h3 : tmv C L'.M.n base s' L'.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L'.M.n base s' L'.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L'.M.n base s' L'.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L'.M.n base s' L'.G.z = tmv C L.M.n base s L.G.z)
    (h : Step L C base s k Q) : Step L' C base s' k Q := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'
  rw [ha, h3] at h2 h3'
  rw [hx, hy, hz] at h3'
  exact h j (hb ▸ hj) X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3'

/-- `mulBody`: for any invariant `Q` of the ladder from the point at `RX`,
`RY`, `ONEP` (`rLadder`) that accepts `O` (as zero and one hold it), for
the scalar at `K`'s slot, `Q 0` accepts what `R` holds at the end; only
`powClob` and `mulBW` change. -/
theorem mulBody_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) (hM : ModOkW c.MP' size c.C.p s.mem base)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (rLadder c) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulBody s fun s' => Rest powClob s s' ∧ Unch base (mulBW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (tbl_bits_ok hc hs hf (i := K) (j := 0) (by decide) (by decide))
    fun s₁ ⟨T₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_rest K₁ (by decide)
  have hf₁ := hf.of_rest K₁
  have e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    O₁.wordsVal (Or.inl (sl_below_bits c h7 hi 0 0)) (by have := sl_le c h7 hi; omega_arith)
  -- The copies.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := ACC) (a := RX) (by decide) (by decide) (by decide))
    fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := PT) (a := RY) (by decide) (by decide) (by decide))
    fun s₃ ⟨x₃, k₃, O₃⟩ => ?_)
  have hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₃ (o := RX) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₄ ⟨x₄, k₄, O₄⟩ => ?_)
  have hs₄ := hs₃.of_rest k₄ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₄ (o := RY) (a := ONEP) (by decide) (by decide) (by decide))
    fun s₅ ⟨x₅, k₅, O₅⟩ => ?_)
  have hs₅ := hs₄.of_rest k₅ (by decide)
  refine WP.mono (copySl_ok hc hs₅ (o := RZ) (a := ZERO) (by decide) (by decide) (by decide))
    fun s₆ ⟨x₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_rest k₆ (by decide)
  have K₁₆ : Rest powClob s s₆ :=
    (K₁.mono (by simp [powClob, clob])).trans
      ((k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))).mono (by simp [powClob, clob]))
  have hf₆ := hf.of_rest K₁₆
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij =>
    O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; omega_arith)
  -- What the copies leave, in terms of `s`.
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
    rw [tbl_unch U h7 (j := 0) (by decide) ht (tbl_apart_slW h7 (by decide) 0 t), T₁ t ht]
  have M₆ : ModOkW c.MP' size c.C.p s₆.mem base := by
    refine modP_of hc ?_
    show sv c base s₆ MP = c.C.p
    rw [e₆ (by decide) (by decide)]; exact hM.val
  have tv : ∀ {i j : Nat}, sv c base s₆ i = sv c base s j →
      tmv c.C c.n base s₆ (c.sl i) = tmv c.C c.n base s (c.sl j) := fun h => by
    show toM _ _ (sv c base s₆ _) = toM _ _ (sv c base s _); rw [h]
  have hstep₆ : Step c.mulLadder c.C base s₆ (sv c base s K) Q :=
    step_congr (L := rLadder c) (L' := c.mulLadder) rfl (tv (e₆ (by decide) (by decide))) (tv (e₆ (by decide) (by decide))) (tv acc₆)
      (tv pt₆) (tv (e₆ (by decide) (by decide))) hstep
  have hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.MP'.n < c.C.p := by
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
  have hR : Q c.mulLadder.nbits (tmv c.C c.n base s₆ c.mulLadder.R.x) (tmv c.C c.n base s₆ c.mulLadder.R.y)
      (tmv c.C c.n base s₆ c.mulLadder.R.z) := by
    show Q _ (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY)) (tmv c.C c.n base s₆ (c.sl RZ))
    rw [tv rx₆, tv ry₆, tv rz₆]; exact hO
  refine WP.mono (VG.Proof.Weierstrass.Arm.Point.ladderP_ok (L := c.mulLadder) (a0 := false) (u := c.umaal) (mulLadLay hc) (mulLadWk hc)
    hc.fp mulLadPt hpR (bitsAt_lt hc (j := 0) (by decide)) hs₆ hf₆ M₆ hlt nofun hstep₆ hR
    (fun t ht => T₆ t (Nat.lt_of_lt_of_le ht (scalarBits_le hc))) (scalarBits_enc hc))
    fun s₇ ⟨K₇, U₇, M₇, L₇, R₇⟩ => ⟨K₁₆.trans K₇, ?_, M₇, L₇, R₇⟩
  rw [mulLadWp_eq] at U₇
  refine (U₁₆.trans U₇).mono fun w hw => ?_
  simp only [mulBW, List.mem_append] at hw ⊢
  rcases hw with (hw | hw) | hw
  · exact .inr hw
  · refine .inl ?_
    rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq]
    simp only [List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    obtain ⟨i, hi, rfl⟩ := hw
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, by
      rcases hi with rfl | rfl | rfl <;> simp, rfl⟩))
  · exact .inl hw

end VG.Proof.Ecdsa.Arm

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.X25519.Arm (Rest Upd wp_mov op2_reg)

variable {c : Cfg}

/-! ## The function -/

/-- Where `vg_<curve>_mul` keeps the callee-saved registers. -/
abbrev mulSW (c : Cfg) : List (Nat × Nat) := [(c.sl nslots, 36)]

/-- What `vg_<curve>_mul` writes. -/
abbrev mulFW (c : Cfg) : List (Nat × Nat) := mulBW c ++ mulSW c

theorem mulSaved_eq (c : Cfg) : c.mulSaved = [(.r4, c.sl 45), (.r5, c.sl 45 + 4), (.r6, c.sl 45 + 8),
    (.r7, c.sl 45 + 12), (.r8, c.sl 45 + 16), (.r9, c.sl 45 + 20),
    (.r11, c.sl 45 + 28), (.lr, c.sl 45 + 32)] := rfl

/-- The registers' words lie past the numbered slots, below the field
arithmetic's own working space and the point functions' slots. -/
theorem save_le_wk (h7 : c.n < 10) : c.sl 45 + 36 ≤ c.wk := by
  rw [sl_eq, wk_eq]; omega_arith

theorem save_le_oAt (h6 : c.n ≤ 6) : c.sl 45 + 36 ≤ Impl.Weierstrass.Point.oAt c.n := by
  rw [sl_eq]
  simp only [Impl.Weierstrass.Point.oAt, Impl.Weierstrass.Point.pAt, Impl.Weierstrass.Point.qAt,
    Impl.Weierstrass.Point.aAt, Impl.Weierstrass.Point.b3At, Impl.Weierstrass.Point.ownAt,
    Impl.Weierstrass.Point.elemBytes, Impl.Weierstrass.Mont.ownAt, Impl.Weierstrass.Mont.ownBytes]
  omega_arith

/-- The registers' words are apart from what the body writes. -/
theorem save_apart (h7 : c.n < 10) : ∀ w ∈ mulBW c, c.sl 45 + 36 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl 45 := by
  intro w hw
  have hwk := save_le_wk (c := c) h7
  simp only [mulBW, mulBX, List.mem_append, VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at hw
  rcases hw with ((hw | hw) | hw) | (hw | hw)
  · simp only [slW, List.mem_map] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    have : i < 45 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact .inr (sl_lt c this)
  · rw [List.mem_singleton.mp hw]; exact .inl hwk
  · unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
    split at hw
    · rw [List.mem_singleton.mp hw]; exact .inl (save_le_oAt ‹_›)
    · simp at hw
  · simp only [slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
    obtain ⟨i, hi, rfl⟩ := hw
    rcases hi with rfl | rfl
    · exact .inr (sl_lt c (by decide))
    · exact .inr (sl_lt c (by decide))
  · rw [List.mem_singleton.mp hw, bitsAt_eq]; left; rw [wk_eq] at hwk; dsimp only; omega_arith

/-- The callee-saved registers' words, by register. -/
theorem mulSaved_bounds (h7 : c.n < 10) : ∀ p ∈ c.mulSaved, p.2 + 4 ≤ size := by
  have := save_le_wk (c := c) h7
  have := wk_le c h7 (M := c.MP') rfl
  rw [mulSaved_eq]; intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem mulSaved_pairwise (c : Cfg) :
    c.mulSaved.Pairwise (fun p q => p.2 + 4 ≤ q.2 ∨ q.2 + 4 ≤ p.2) := by
  rw [mulSaved_eq]; simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, false_implies, implies_true]
  generalize c.sl 45 = x
  omega

theorem mulSaved_regs (c : Cfg) : (c.mulSaved.map Prod.fst).Nodup ∧ ∀ p ∈ c.mulSaved, p.1 ≠ .r12 := by
  rw [mulSaved_eq]
  refine ⟨by simp only [List.map_cons, List.map_nil]; decide, fun p hp => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- `vg_<curve>_mul`, from the working space at `r0` (`base`), its `8192`
bytes the only memory it may access, and what `mulBody_ok` needs of them:
it returns with the callee-saved registers and `sp` kept and `r12 = ws`,
having changed only `mulFW`, with `Q 0` accepting what `R` holds. -/
theorem mulFn_ok (hc : CfgOk c) {s : State} {base : Addr} (hb : State.addr (s.gpr .r0) = base)
    (hwr : s.wr = [⟨base, 8192⟩]) (hfit : base.toNat + 8192 ≤ 2 ^ 32)
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (rLadder c) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa c.mulFn s fun s' => abiPreserved s s' ∧ s'.gpr .r12 = s.gpr .r0 ∧ s'.rd = s.rd ∧
      s'.wr = s.wr ∧ Unch base (mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hsv := save_le_wk (c := c) h7
  have hsz : size = 4096 := rfl
  rw [Cfg.mulFn]
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => ?_)
  have hs₁ : Scr s₁ base size := ⟨by rw [u₁.gpr]; exact hb, ⟨8192, by decide, by decide,
    by rw [u₁.wr, hwr]; simp⟩, by omega, by decide⟩
  have hf₁ : Far s₁ base 8192 := ⟨by rw [u₁.wr, hwr]; simp, hfit⟩
  refine WP.mono (strs_ok hs₁ c.mulSaved (mulSaved_bounds h7) (mulSaved_pairwise c))
    fun s₂₀ ⟨K₂₀, O₂₀, V₂₀⟩ => ?_
  refine WP.seq (wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  have K₂ : Rest [.lr] s₁ s₂ := (K₂₀.mono fun _ h => absurd h List.not_mem_nil).trans (u₂.rest (by simp))
  have O₂ : Outs base (c.mulSaved.map fun p => (p.2, 4)) s₁.mem s₂.mem := by rw [u₂.mem]; exact O₂₀
  have V₂ : ∀ p ∈ c.mulSaved, s₂.mem.readW (off base p.2) 32 = s₁.gpr p.1 := fun p hp => by
    rw [u₂.mem]; exact V₂₀ p hp
  have l₂ : s₂.gpr .lr = s.gpr .r10 := by rw [u₂.gpr, K₂₀.gpr _ (by simp), u₁.other _ (by decide)]
  have hs₂ := hs₁.of_rest K₂ (by decide)
  have hf₂ := hf₁.of_rest K₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi => by
    have := sl_lt c (j := 45) hi
    have := sl_le c h7 hi
    refine (VG.Proof.Weierstrass.Arm.Outs.wordsVal O₂ (fun r hr => ?_) (by omega_arith)).trans ?_
    · rw [mulSaved_eq] at hr
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> left <;> dsimp only <;> omega_arith
    · rw [u₁.mem]
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hstep₂ : Step (rLadder c) c.C base s₂ (sv c base s₂ K) Q := by
    rw [e₂ (by decide)]
    exact step_congr rfl (tv (by decide)) (tv (by decide)) (tv (by decide)) (tv (by decide))
      (tv (by decide)) hstep
  have hO₂ : Q c.ladderCfg.nbits (tmv c.C c.n base s₂ (c.sl ZERO)) (tmv c.C c.n base s₂ (c.sl ONEP))
      (tmv c.C c.n base s₂ (c.sl ZERO)) := by
    rw [tv (by decide), tv (by decide)]; exact hO
  refine WP.seq (WP.mono (mulBody_ok hc hs₂ hf₂ (modP_of hc (by
      show sv c base s₂ MP = _; rw [e₂ (by decide)]; exact hmp))
    (by rw [e₂ (by decide)]; exact hap) (by rw [e₂ (by decide)]; exact hb3)
    (by rw [e₂ (by decide)]; exact hone) (by rw [e₂ (by decide)]; exact hzero)
    (by rw [e₂ (by decide)]; exact hqx) (by rw [e₂ (by decide)]; exact hqy) hstep₂ hO₂)
    fun s₃₀ ⟨K₃, U₃₀, M₃, L₃₀, R₃₀⟩ => ?_)
  refine WP.seq (wp_mov (op2_reg _ _) fun s₃ u₃ => WP.block_nil ?_)
  have l₃ : s₃.gpr .r10 = s.gpr .r10 := by rw [u₃.gpr, K₃.gpr _ (by decide), l₂]
  have U₃ : Unch base (mulBW c) s₂.mem s₃.mem := by rw [u₃.mem]; exact U₃₀
  have L₃ : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s₃.mem base x c.n < c.C.p := by
    rw [u₃.mem]; exact L₃₀
  have R₃ : Q 0 (tmv c.C c.n base s₃ (c.sl RX)) (tmv c.C c.n base s₃ (c.sl RY))
      (tmv c.C c.n base s₃ (c.sl RZ)) := by
    show Q 0 (toM _ _ (wordsVal s₃.mem _ _ _)) (toM _ _ (wordsVal s₃.mem _ _ _)) (toM _ _ (wordsVal s₃.mem _ _ _))
    rw [u₃.mem]; exact R₃₀
  have hs₃ := (hs₂.of_rest K₃ (by decide)).of_rest (u₃.rest (ws := [.r10]) (by simp)) (by decide)
  refine WP.mono (ldrs_ok hs₃ c.mulSaved (mulSaved_bounds h7) (mulSaved_regs c).1 (mulSaved_regs c).2)
    fun s₄ ⟨M₄, K₄, V₄⟩ => ?_
  -- The words of the registers, kept by the body.
  have kept : ∀ p ∈ c.mulSaved, s₃.mem.readW (off base p.2) 32 = s₂.mem.readW (off base p.2) 32 := by
    intro p hp
    refine VG.Proof.Weierstrass.Arm.Unch.readW32 U₃ (fun w hw => ?_) (by have := mulSaved_bounds h7 p hp; omega_arith)
    have hp' : c.sl 45 ≤ p.2 ∧ p.2 + 4 ≤ c.sl 45 + 36 := by
      rw [mulSaved_eq] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
    rcases save_apart h7 w hw with h | h <;> [exact .inl (by omega_arith); exact .inr (by omega_arith)]
  refine ⟨⟨fun r hr => ?_, by rw [K₄.sp, u₃.sp, K₃.sp, K₂.sp, u₁.sp]⟩, ?_,
    by rw [K₄.rd, u₃.rd, K₃.rd, K₂.rd, u₁.rd], by rw [K₄.wr, u₃.wr, K₃.wr, K₂.wr, u₁.wr], ?_, ?_, ?_⟩
  · by_cases h10 : r = .r10
    · subst h10
      rw [K₄.gpr _ (by simp only [mulSaved_eq, List.map_cons, List.map_nil]; decide), l₃]
    have hp : ∃ d, (r, d) ∈ c.mulSaved := by
      simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [mulSaved_eq]
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | exact absurd rfl h10 |
        exact ⟨_, by repeat (first | exact List.mem_cons_self | apply List.mem_cons_of_mem)⟩
    obtain ⟨d, hd⟩ := hp
    rw [V₄ _ hd, kept _ hd, V₂ _ hd, u₁.other _ (by
      intro h; subst h; simp [preserved] at hr)]
  · rw [K₄.gpr _ (by simp only [mulSaved_eq, List.map_cons, List.map_nil]; decide), u₃.other _ (by decide),
      K₃.gpr _ (by decide), K₂.gpr _ (by decide), u₁.gpr]
  · rw [M₄]
    have := (VG.Proof.Weierstrass.Arm.Outs.unch O₂).trans U₃
    rw [u₁.mem] at this
    refine this.cover fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [mulSaved_eq] at hw
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      refine ⟨(c.sl nslots, 36), List.mem_append_right _ (List.mem_singleton_self _), ?_⟩
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by dsimp only [nslots]; omega_arith, by dsimp only [nslots]; omega_arith⟩
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
  · rw [M₄]; exact L₃
  · show Q 0 (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _)) (toM _ _ (wordsVal s₄.mem _ _ _))
    rw [M₄]; exact R₃

/-! ## The call -/

/-- What `vg_<curve>_mul` needs on entry, and gives its caller, at the
working space `base`: the constants, `Q`, the invariant `Q'` of the ladder
from `Q` and that it accepts `O`. -/
structure MulIn (c : Cfg) (base : Addr) (Q' : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (m : Mem) : Prop where
  mp : wordsVal m base (c.sl MP) c.n = c.C.p
  ap : wordsVal m base (c.sl AP) c.n < c.C.p
  b3 : wordsVal m base (c.sl B3P) c.n < c.C.p
  one : wordsVal m base (c.sl ONEP) c.n < c.C.p
  zero : wordsVal m base (c.sl ZERO) c.n < c.C.p
  qx : wordsVal m base (c.sl RX) c.n < c.C.p
  qy : wordsVal m base (c.sl RY) c.n < c.C.p

/-- A call of `vg_<curve>_mul` on the point at `px`, `py`, from the working
space at `r12`: for any invariant `Q` of the ladder from that point that
accepts `O`, `Q 0` accepts what `R` holds after it; only `r0`–`r4`, `r10`,
`R`'s first two slots and `mulFW` change. -/
theorem mulAt_ok (hc : CfgOk c) (C : Impl.Weierstrass.Mul.Curve) (hnf : c.mulFn.noFrames = true)
    {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {px py : Nat} (hpx : px < 45) (hpy : py < 45) (hpxr : px ∉ [RX, RY]) (hpyr : py ∉ [RX, RY])
    (hmp : sv c base s MP = c.C.p)
    (hap : sv c base s AP < c.C.p) (hb3 : sv c base s B3P < c.C.p) (hone : sv c base s ONEP < c.C.p)
    (hzero : sv c base s ZERO < c.C.p) (hqx : sv c base s px < c.C.p) (hqy : sv c base s py < c.C.p)
    {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (pLadder c px py) c.C base s (sv c base s K) Q)
    (hO : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
      (tmv c.C c.n base s (c.sl ZERO))) :
    WP isa (c.mulAt C px py) s fun s' => Rest [.r10, .r0, .r1, .r2, .r3, .r4] s s' ∧
      Unch base (slW c [RX, RY] ++ mulFW c) s.mem s'.mem ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY)) (tmv c.C c.n base s' (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hpxr hpyr
  rw [Cfg.mulAt]
  -- The copies and the moves before the call.
  refine WP.seq ?_
  simp only [List.append_assoc]
  refine WP.block_append (WP.mono (copySl_ok hc hs (o := RX) (a := px) (by decide) hpx
    (Ne.symm hpxr.1)) fun s₁ ⟨x₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_rest k₁ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := RY) (a := py) (by decide) hpy
    (Ne.symm hpyr.2)) fun s₂ ⟨x₂, k₂, O₂⟩ => ?_)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have k₄ : Rest [.r10, .r0, .r4] s s₄ :=
    (k₁.mono (by simp)).trans ((k₂.mono (by simp)).trans ((u₃.rest (by simp)).trans (u₄.rest (by simp))))
  have m₄ : s₄.mem = s₂.mem := by rw [u₄.mem, u₃.mem]
  have hs₄ := hs.of_rest k₄ (by decide)
  have hf₄ := hf.of_rest k₄
  have g10 : s₄.gpr .r10 = s.gpr .lr := by
    rw [u₄.other _ (by decide), u₃.gpr, k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have g0 : s₄.gpr .r0 = s.gpr .r12 := by
    rw [u₄.gpr, u₃.other _ (by decide), k₂.gpr _ (by decide), k₁.gpr _ (by decide)]
  have o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij =>
    O.wordsVal (sl_apart c hij) (by have := sl_le c h7 hi; omega_arith)
  have e₄ : ∀ {i}, i < 45 → i ≠ RX → i ≠ RY → sv c base s₄ i = sv c base s i := fun hi h1 h2 => by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact (o O₂ hi h2).trans (o O₁ hi h1)
  have rx₄ : sv c base s₄ RX = sv c base s px := by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact (o O₂ (by decide) (by decide)).trans x₁
  have ry₄ : sv c base s₄ RY = sv c base s py := by
    show wordsVal s₄.mem _ _ _ = _; rw [m₄]; exact x₂.trans (o O₁ hpy hpyr.1)
  have tv : ∀ {i j}, sv c base s₄ i = sv c base s j → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl j) :=
    fun h => by show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _); rw [h]
  have hstep₄ : Step (rLadder c) c.C base s₄ (sv c base s₄ K) Q := by
    rw [e₄ (by decide) (by decide) (by decide)]
    exact step_congr (L := pLadder c px py) rfl (tv (e₄ (by decide) (by decide) (by decide)))
      (tv (e₄ (by decide) (by decide) (by decide))) (tv rx₄) (tv ry₄)
      (tv (e₄ (by decide) (by decide) (by decide))) hstep
  have hO₄ : Q c.ladderCfg.nbits (tmv c.C c.n base s₄ (c.sl ZERO)) (tmv c.C c.n base s₄ (c.sl ONEP))
      (tmv c.C c.n base s₄ (c.sl ZERO)) := by
    rw [tv (e₄ (i := ZERO) (by decide) (by decide) (by decide)), tv (e₄ (i := ONEP) (by decide) (by decide) (by decide))]
    exact hO
  have hcov : Covers [⟨base, 8192⟩] s₄.wr := by
    have h := hf₄.write (d := 0) (n := 8192) (by omega)
    simp only [off, BitVec.add_zero] at h
    exact Covers.one h
  have e0 : ∀ t : State, t.gpr .r0 = s.gpr .r12 → State.addr (t.gpr .r0) = base := fun t h => by
    rw [h]; exact hs.wb
  refine WP.seq (WP.callCalls (k := ⟨fun t => t.wr = [⟨base, 8192⟩] ∧ t.gpr .r0 = s.gpr .r12 ∧
        t.mem = s₄.mem,
      fun t t' => t'.gpr .r12 = t.gpr .r0 ∧ Unch base (mulFW c) t.mem t'.mem ∧
        (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t'.mem base x c.n < c.C.p) ∧
        Q 0 (tmv c.C c.n base t' (c.sl RX)) (tmv c.C c.n base t' (c.sl RY)) (tmv c.C c.n base t' (c.sl RZ)),
      fun _ _ => True⟩)
    (fun t ⟨hw, h0, hm⟩ => by
      have hb := e0 t h0
      have sv_t : ∀ i, sv c base t i = sv c base s₄ i := fun i => by
        show wordsVal t.mem _ _ _ = wordsVal s₄.mem _ _ _; rw [hm]
      have tm_t : ∀ i, tmv c.C c.n base t (c.sl i) = tmv c.C c.n base s₄ (c.sl i) := fun i => by
        show toM _ _ (sv c base t i) = toM _ _ (sv c base s₄ i); rw [sv_t]
      obtain ⟨tr, t', he, A, R12, -, -, U, L, R⟩ := mulFn_ok hc hb hw hf.nowrap
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hmp)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hap)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hb3)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hone)
        (by rw [sv_t, e₄ (by decide) (by decide) (by decide)]; exact hzero)
        (by rw [sv_t, rx₄]; exact hqx) (by rw [sv_t, ry₄]; exact hqy)
        (by rw [sv_t]; exact step_congr rfl (tm_t _) (tm_t _) (tm_t _) (tm_t _) (tm_t _) hstep₄)
        (by rw [tm_t, tm_t]; exact hO₄)
      exact ⟨tr, t', he, A, R12, U, L, R⟩)
    (rd := []) (wr := [⟨base, 8192⟩])
    ⟨by rw [State.withRegions_wr],
      by rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), g0],
      by rw [State.withRegions_mem, State.callEntry_mem]⟩
    (Covers.right hcov) hcov ?_ hnf)
  intro s₇ r₇ w₇ p₇ _ hp₇ _ ⟨R, U, L, E⟩
  simp only [State.withRegions_mem, State.callEntry_mem, State.withRegions_gpr] at R U L E
  rw [State.callEntry_gpr _ (by decide), g0] at R
  refine wp_mov (op2_reg _ _) fun s₈ u₈ => WP.block_nil ?_
  have hm : s₈.mem = s₇.mem := u₈.mem
  refine ⟨⟨fun r hr => ?_, by rw [u₈.rd, r₇, k₄.rd], by rw [u₈.wr, w₇, k₄.wr],
    by rw [u₈.sp, p₇, k₄.sp]⟩, ?_, by rw [hm]; exact L, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    obtain ⟨h10, h0, h1, h2, h3, h4⟩ := hr
    by_cases hlr : r = .lr
    · subst hlr
      rw [u₈.gpr, hp₇ _ (by decide) (by decide), g10]
    by_cases h12 : r = .r12
    · subst h12
      rw [u₈.other _ (by decide), R]
    have hpres : r ∈ preserved := by revert h10 h0 h1 h2 h3 h4 h12 hlr; cases r <;> decide
    rw [u₈.other _ hlr, hp₇ r hpres hlr, k₄.gpr r (by simp [h10, h0, h4])]
  · rw [hm]
    have U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := by
      have := O₁.unch.trans O₂.unch
      exact this.mono fun w hw => by simpa using hw
    rw [m₄] at U
    simpa only [List.append_assoc] using U₂.trans U
  · show Q 0 (toM _ _ (wordsVal s₈.mem _ _ _)) (toM _ _ (wordsVal s₈.mem _ _ _)) (toM _ _ (wordsVal s₈.mem _ _ _))
    rw [hm]; exact E

/-! ## What `vg_<curve>_mul` writes besides the ladder -/

/-- `ACC`, `PT` (its copy of `Q`), the table of `k`'s bits and the words past
the numbered slots where it keeps the callee-saved registers. -/
abbrev genX (c : Cfg) : List (Nat × Nat) := slW c [ACC, PT] ++ [(bitsAt c.n 0, 64 * c.n), (c.sl nslots, 36)]

theorem apart_genX (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hl : i ∉ [ACC, PT]) :
    ∀ w ∈ genX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hl) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (Nat.le_trans (sl_below_bits c h7 hi 0 0) (Nat.le_add_right _ _))
  · exact Or.inl (sl_lt c (j := nslots) hi)

theorem tbl_apart_genX (h7 : c.n < 10) {j t : Nat} (hj : j ≠ 0) (ht : t < 64 * c.n) :
    ∀ w ∈ genX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW h7 (by decide) j t) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact tbl_apart_tbl hj ht _ (List.mem_singleton_self _)
  · refine Or.inr ?_
    rw [bitsAt_eq, sl_eq]; dsimp only [nslots]; omega_arith

theorem fixedOk_genX (h7 : c.n < 10) : FixedOk c (genX c) := by
  refine (fixedOk_slW (by decide)).append fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact fixedOk_tbl h7 0 _ (List.mem_singleton_self _)
  · exact Or.inr (Nat.le_of_lt_succ (Nat.lt_succ_of_le (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (by decide)))))

theorem genX_le (h7 : c.n < 10) : ∀ w ∈ genX c, w.1 + w.2 ≤ 8192 := by
  intro w hw
  simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  have := sl_le c h7 (i := 44) (by decide)
  have := bitsAt_le c h7 (j := 0) (by decide)
  rw [sl_eq] at *
  rcases hw with ⟨i, rfl | rfl, rfl⟩ | rfl | rfl <;> simp only [sl_eq, ACC, PT, nslots] at * <;> omega_arith

/-- Everything `vg_<curve>_mul` writes is at or past the temporary slot. -/
theorem mulFW_ge (h7 : c.n < 10) : ∀ w ∈ mulFW c, c.sl TMP ≤ w.1 := by
  intro w hw
  have hwk := save_le_wk (c := c) h7
  simp only [mulFW, mulBW, mulBX, mulSW, List.mem_append, VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq,
    slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
  rw [wk_eq, sl_eq] at hwk
  rcases hw with (((⟨j, hj, rfl⟩ | hw) | hw) | (⟨j, hj, rfl⟩ | hw)) | hw
  · rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [sl_eq, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP] <;> omega
  · rw [hw, wk_eq, sl_eq]; simp only [TMP]; omega
  · unfold VG.Proof.Weierstrass.Arm.Point.ptW at hw
    split at hw
    · rw [List.mem_singleton.mp hw, show c.ladderCfg.M.n = c.n from rfl]
      have h1 := save_le_oAt (c := c) ‹_›
      rw [sl_eq] at h1 ⊢; simp only [TMP]; omega
    · simp at hw
  · rcases hj with rfl | rfl <;> simp only [sl_eq, ACC, PT, TMP] <;> omega
  · rw [hw, bitsAt_eq, sl_eq]; simp only [TMP]; omega
  · rw [hw]; simp only [sl_eq, nslots, TMP]; omega

/-! ## `R = [k]P`, by the call or the ladder -/

/-- `qMul`: for any invariant `Q` of the ladder from the point at `px`, `py`,
`ONEP` that accepts `O`, `Q 0` accepts what `R` holds at the end, for the
scalar `k` at `K`'s slot (for the call) or whose bits are the table (for the
ladder), from `R = O`; only `powClob`, the ladder's slots and `genX` change. -/
theorem qMul_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {g : Reg → BitVec 32} (F : Fixed c base g s.mem) {px py : Nat} (hp : PtSlots px py)
    (hpx : sv c base s px < c.C.p) (hpy : sv c base s py < c.C.p)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    {k : Nat} {Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hstep : Step (pLadder c px py) c.C base s k Q c.qA0) (hO : Q (8 * c.C.len) 0 1 0)
    (hk : c.mul.isSome → sv c base s K = k)
    (ht : c.mul = none → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0) :
    WP isa (c.qMul px py) s fun t => Rest powClob s t ∧
      Unch base (VG.Proof.Weierstrass.Arm.Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
      ModOkW c.MP' size c.C.p t.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal t.mem base x c.n < c.C.p) ∧
      Q 0 (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have tone : toM c.C.p (2 ^ (64 * c.n)) (2 ^ (64 * c.n) % c.C.p) = 1 := toM_one hpR
  unfold Cfg.qMul
  cases hm : c.mul with
  | none =>
    simp only
    have hlt : ∀ x ∈ ladR (pLadder c px py), wordsVal s.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, px, py, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c base s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F.ap (hmont _)
      · exact lt_of_eq_of_lt F.b3p (hmont _)
      · exact hpx
      · exact hpy
      · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))
      · exact lt_of_eq_of_lt hrx (by omega)
      · exact lt_of_eq_of_lt hry (hmont _)
      · exact lt_of_eq_of_lt hrz (by omega)
    have hR : Q (pLadder c px py).nbits (tmv c.C c.n base s (pLadder c px py).R.x)
        (tmv c.C c.n base s (pLadder c px py).R.y) (tmv c.C c.n base s (pLadder c px py).R.z) := by
      show Q _ (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)) (toM _ _ (sv c base s RZ))
      rw [hrx, hry, hrz, toM_cmont hc, toM_zero]
      exact hO
    refine WP.mono (VG.Proof.Weierstrass.Arm.Point.ladderP_ok (L := pLadder c px py) (k := k) (a0 := c.qA0) (u := c.umaal)
      (pLadLay hc hp) (pLadWk hc hp) hc.fp (pLadPt hp) hpR (bitsAt_lt hc (j := 0) (by decide)) hs hf
      (modP_of hc F.mp) hlt (fun h => by
        simp only [Cfg.qA0, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.2.2) hstep hR (fun t h => ht hm t (Nat.lt_of_lt_of_le h (scalarBits_le hc)))
      (scalarBits_enc hc)) fun t ⟨K, U, M, L, R⟩ => ⟨K, U.mono fun w hw => List.mem_append_left _ hw, M, L, R⟩
  | some C =>
    simp only
    have hpx' := hp px (List.mem_cons_self)
    have hpy' := hp py (List.mem_cons_of_mem _ List.mem_cons_self)
    have hpxr : px ∉ [RX, RY] := fun h => hpx'.2.2.2.2 (by
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hpyr : py ∉ [RX, RY] := fun h => hpy'.2.2.2.2 (by
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · rw [List.mem_singleton.mp h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
    have hk' : sv c base s K = k := hk (by rw [hm]; rfl)
    have hq : c.qA0 = false := by simp only [Cfg.qA0, hm, Option.isNone_some, Bool.false_and]
    rw [hq] at hstep
    have hstep' : Step (pLadder c px py) c.C base s (sv c base s K) Q := by rw [hk']; exact hstep
    have hO' : Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl ZERO)) (tmv c.C c.n base s (c.sl ONEP))
        (tmv c.C c.n base s (c.sl ZERO)) := by
      show Q _ (toM _ _ (sv c base s ZERO)) (toM _ _ (sv c base s ONEP)) (toM _ _ (sv c base s ZERO))
      rw [show sv c base s ZERO = 0 from F.zero, show sv c base s ONEP = _ from F.onep, toM_zero, tone]
      exact hO
    refine WP.mono (mulAt_ok (px := px) (py := py) (Q := Q) hc C (hc.mulNf C hm) hs hf hpx'.1 hpy'.1
      hpxr hpyr F.mp (lt_of_eq_of_lt F.ap (hmont _)) (lt_of_eq_of_lt F.b3p (hmont _))
      (lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega))) (lt_of_eq_of_lt F.zero (by omega)) hpx hpy
      hstep' hO')
      fun t ⟨K, U, L, R⟩ => ⟨K.mono (by simp [powClob, clob]), ?_, ?_, L, R⟩
    · refine U.mono fun w hw => ?_
      simp only [mulFW, mulBW, mulBX, mulSW, genX, List.mem_append] at hw ⊢
      rcases hw with hw | ((hw | hw | hw) | hw)
      · refine .inl ?_
        rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq]
        simp only [slW, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
        obtain ⟨i, hi, rfl⟩ := hw
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨i, by
          rcases hi with rfl | rfl <;> simp, rfl⟩))
      · exact .inl hw
      · exact .inr (.inl hw)
      · exact .inr (.inr (by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self))
      · exact .inr (.inr (by rw [List.mem_singleton.mp hw]; exact List.mem_cons_of_mem _ List.mem_cons_self))
    · have hmp : wordsVal t.mem base (c.sl MP) c.n = wordsVal s.mem base (c.sl MP) c.n := by
        refine U.wordsVal (fun w hw => .inl ?_) ?_
        · have h12 := sl_lt c (i := MP) (j := TMP) (by decide)
          rcases List.mem_append.mp hw with hw | hw
          · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl <;> exact Nat.le_trans h12 (Nat.le_trans (Nat.le_add_right _ _)
              (sl_lt c (by decide)))
          · exact Nat.le_trans h12 (mulFW_ge h7 w hw)
        · have := sl_le c h7 (i := MP) (by decide); dsimp only [size] at this; omega
      exact modP_of hc (hmp.trans F.mp)

end VG.Proof.Ecdsa.Arm
