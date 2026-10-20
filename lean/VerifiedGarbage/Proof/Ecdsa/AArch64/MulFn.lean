module

public import VerifiedGarbage.Proof.Ecdsa.AArch64.Fixed
import VerifiedGarbage.Proof.Ecdsa.AArch64.Lays
import VerifiedGarbage.Proof.Ecdsa.AArch64.Stages
public import VerifiedGarbage.Proof.Weierstrass.AArch64.Ladder
import VerifiedGarbage.Proof.Weierstrass.AArch64.Rep
import VerifiedGarbage.Proof.Weierstrass.AArch64.Bits
import VerifiedGarbage.Proof.Weierstrass.AArch64.Copy
import VerifiedGarbage.Proof.Weierstrass.AArch64.SetConst
import VerifiedGarbage.Proof.Ecdsa.AArch64.Setup
import VerifiedGarbage.Proof.Weierstrass.Pow
import VerifiedGarbage.Proof.Weierstrass.AArch64.MontCall
import VerifiedGarbage.Proof.Framework.AArch64.Call
import VerifiedGarbage.Proof.Framework.Block

/-!
# `vg_<curve>_mul` on AArch64, and `R = [k]P` by its call

`Cfg.mulBody`: the table of `k`'s bits (`bits_ok`), from the scalar in `K`'s
slot, `Q` (in `R`'s first two slots) copied to `ACC` and `PT`, `R` the point
at infinity (copies of zero and one, `copy_ok`), then `R = [k]Q` by the
ladder (`ladder_ok`, `step_rep`), which reads `p`, `a R` and `3 b R` (at
`BM`'s slot, where the contract has it) and writes only its slots, `R`'s,
`ACC`'s, `PT`'s and the table of bits (`mulBody_ok`). `Cfg.mulFn` runs it
between keeping `x19` and `invRegs` (`invKept`) in the words past the table
and restoring them (`mulFn_ok`). `mulAt_ok`: `R = [k]P` by a call of the function, with `P`
copied to `R`'s first two slots and `3 b R` to `BM`'s slot, then `b R` back,
which keeps the signature's constants (`Fixed`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- Where `vg_<curve>_mul`'s products keep their temporary area (`invTmp`,
`Cfg.mulLadder`): `TMP`'s slot, or past the words where it keeps `invKept`. -/
def MulTmp (c : Cfg) : Prop := c.invTmp = slot c.n TMP ∨ c.mulSave + c.invSaveLen ≤ c.invTmp

/-- What `vg_<curve>_mul`'s body writes: `R`'s slots, `ACC`'s and `PT`'s (its
copy of `Q`), the ladder's, its products' temporary area and the table of
`k`'s bits. -/
abbrev mulW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++
    [(c.invTmp, 8 * c.n), (bitsAt c.n 0, 64 * c.n)]

/-- What the function writes: its body's, and the words past the table, where
it keeps `invKept`. -/
abbrev mulWF (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++
    [(c.invTmp, 8 * c.n), (bitsAt c.n 0, 64 * c.n + c.invSaveLen)]

/-- The point `Q` in `R`'s first two slots, as the proofs decode it. -/
abbrev ptQ (c : Cfg) (base : Addr) (s : State) : Point c.C :=
  .affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))

theorem ladWM_eq (c : Cfg) : ladW c.mulLadder = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ] ++ [(c.invTmp, 8 * c.n)] := rfl

/-- `R = [k]Q` for the `k` in `K`'s slot and the point `Q` on the curve in
`R`'s first two slots, with the table of `k`'s bits, from `p`, zero, one,
`a R` and `3 b R` in their slots. -/
theorem mulBody_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8) (hL : LadLay c.mulLadder size) (hA : LadA c.mulLadder)
    (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hb3 : sv c base s BM = c.mont (3 * c.C.b))
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulBody s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (mulW c) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  have hb4 := bitsAt0_le c h7
  have sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
  have ap : ∀ {i j}, i ≠ j → i ≠ TMP → j ≠ TMP → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i :=
    fun h hi hj => by rcases sl_apart c h (.inl hi) (.inl hj) with h | h <;> omega
  have m8 := sl_mod8 c
  rw [Cfg.mulBody]
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (by omega) (sz (i := K) (by decide)) hsz
    (by rcases h4 with h4 | h4 | h4 <;> rw [sl_eq c K (by decide), h4] <;> decide) (by omega)
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  -- `Q` to `ACC` and `PT`, and `R` the point at infinity.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl ACC) (a := c.sl RX)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide) (by decide) (by decide))) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₂ (o := c.sl PT) (a := c.sl RY)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide) (by decide) (by decide))) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₃ (o := c.sl RX) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide) (by decide) (by decide))) fun s₄ ⟨v₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₄ (o := c.sl RY) (a := c.sl ONEP)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide) (by decide) (by decide))) fun s₅ ⟨v₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₅ (o := c.sl RZ) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (m8 _) (m8 _) (ap (by decide) (by decide) (by decide))) fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- What each copy leaves.
  have U₂ : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slW c [ACC]) s.mem s₂.mem := U₁.trans O₂.unch
  have U₃ : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slW c [ACC, PT]) s.mem s₃.mem := U₂.trans O₃.unch
  have U₄ : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slW c [ACC, PT, RX]) s.mem s₄.mem :=
    U₃.trans O₄.unch
  have U₅ : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slW c [ACC, PT, RX, RY]) s.mem s₅.mem :=
    U₄.trans O₅.unch
  have U₆ : Unch base ([(bitsAt c.n 0, 64 * c.n)] ++ slW c [ACC, PT, RX, RY, RZ]) s.mem s₆.mem :=
    U₅.trans O₆.unch
  have U₂₆ : Unch base (slW c [PT, RX, RY, RZ]) s₂.mem s₆.mem :=
    ((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch
  have U₃₆ : Unch base (slW c [RX, RY, RZ]) s₃.mem s₆.mem := (O₄.unch.trans O₅.unch).trans O₆.unch
  have U₄₆ : Unch base (slW c [RY, RZ]) s₄.mem s₆.mem := O₅.unch.trans O₆.unch
  have U₅₆ : Unch base (slW c [RZ]) s₅.mem s₆.mem := O₆.unch
  have abt : ∀ {i}, i < 45 → ∀ {l : List Nat}, i ∉ l → i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 → (∀ j ∈ l, j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82) →
      ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)] ++ slW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi _ hl ha hb => apart_append (apart_tbl hi 0 h7) (apart_slW hl ha hb)
  have e₁ := fun {i} (hi : i < 45) => sv_unch U₁ h7 hn hi (apart_tbl hi 0 h7)
  have acc₆ : sv c base s₆ ACC = sv c base s RX :=
    (sv_unch U₂₆ h7 hn (i := ACC) (by decide) (apart_slW (by decide))).trans (v₂.trans (e₁ (by decide)))
  have pt₆ : sv c base s₆ PT = sv c base s RY :=
    (sv_unch U₃₆ h7 hn (i := PT) (by decide) (apart_slW (by decide))).trans
      (v₃.trans (sv_unch U₂ h7 hn (i := RY) (by decide) (abt (by decide) (by decide) (by decide) (by decide))))
  have rx₆ : sv c base s₆ RX = 0 :=
    (sv_unch U₄₆ h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans
      (v₄.trans ((sv_unch U₃ h7 hn (i := ZERO) (by decide) (abt (by decide) (by decide) (by decide) (by decide))).trans hz))
  have one₄ : sv c base s₄ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (sv_unch U₄ h7 hn (i := ONEP) (by decide) (abt (by decide) (by decide) (by decide) (by decide))).trans hone
  have ry₆ : sv c base s₆ RY = c.mont 1 := by
    have h := (sv_unch U₅₆ h7 hn (i := RY) (by decide) (apart_slW (by decide))).trans (v₅.trans one₄)
    rw [show c.mont 1 = 2 ^ (64 * c.n) % c.C.p by show 1 * c.R % c.C.p = _; rw [Nat.one_mul]; rfl]
    exact h
  have rz₆ : sv c base s₆ RZ = 0 :=
    v₆.trans ((sv_unch U₅ h7 hn (i := ZERO) (by decide) (abt (by decide) (by decide) (by decide) (by decide))).trans hz)
  have e₆ := fun {i} (hi : i < 45) (hl : i ∉ [ACC, PT, RX, RY, RZ]) (ha : i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82) =>
    sv_unch U₆ h7 hn hi (abt hi hl ha (by decide))
  have mp₆ : sv c base s₆ MP = c.C.p := (e₆ (i := MP) (by decide) (by decide) (by decide)).trans hmp
  have ap₆ : sv c base s₆ AP = c.mont c.C.a := (e₆ (i := AP) (by decide) (by decide) (by decide)).trans hap
  have b3₆ : sv c base s₆ BM = c.mont (3 * c.C.b) := (e₆ (i := BM) (by decide) (by decide) (by decide)).trans hb3
  have one₆ : sv c base s₆ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (e₆ (i := ONEP) (by decide) (by decide) (by decide)).trans hone
  have U₂₆' : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem :=
    ((((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch)
  have k₆' : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch U₂₆' h7 (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t)]
    exact b₁ t ht
  -- The ladder.
  have hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, BM, ACC, PT, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₆ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt ap₆ (hmont _)
    · exact lt_of_eq_of_lt b3₆ (hmont _)
    · rw [acc₆]; exact hqx
    · rw [pt₆]; exact hqy
    · exact lt_of_eq_of_lt one₆ (Nat.mod_lt _ (by omega))
    · exact lt_of_eq_of_lt rx₆ (by omega)
    · exact lt_of_eq_of_lt ry₆ (hmont _)
    · exact lt_of_eq_of_lt rz₆ (by omega)
  have hG : Rep c.C (tmv c.C c.n base s₆ (c.sl ACC)) (tmv c.C c.n base s₆ (c.sl PT))
      (tmv c.C c.n base s₆ (c.sl ONEP)) (ptQ c base s) := by
    show Rep c.C (toM _ _ (sv c base s₆ ACC)) (toM _ _ (sv c base s₆ PT)) (toM _ _ (sv c base s₆ ONEP))
      (Point.affine (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)))
    rw [acc₆, pt₆, one₆, toM_one hpR]
    exact rep_affine' hC _ _
  have hstep := step_rep (L := c.mulLadder) (k := sv c base s K) hC hQ
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ AP) = _; rw [ap₆]; exact toM_cmont hc _)
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ BM) = _; rw [b3₆]; exact toM_cmont hc _) hG
  have hR : Rep c.C (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY))
      (tmv c.C c.n base s₆ (c.sl RZ)) (mul (sv c base s K >>> (64 * c.n)) (ptQ c base s)) := by
    show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [rx₆, ry₆, rz₆, toM_cmont hc, toM_zero, shiftRight_eq_zero (wordsVal_lt _ _ _ _), mul_zero_pt]
    exact rep_infinity' hC
  have hk1 : ∀ r ∈ [Reg.x1, .x2, .x5, .x16, .x17, .x19], r ∈ powClob c.n := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [powClob, clob]
  have hk2 : ∀ r ∈ [Reg.x1], r ∈ powClob c.n := fun r hr => hk1 r (by
    simp only [List.mem_singleton] at hr; simp [hr])
  refine WP.mono (ladder_ok hL hA hpR hs₆ (modOkA_inv hc (modP_of hc mp₆) (.inl rfl) rfl rfl) hlt hstep hR k₆')
    fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, ?_, modP_of hc M'.val, L', ?_⟩
  · exact ((((((k₁.mono hk1).trans (k₂.mono hk2)).trans (k₃.mono hk2)).trans (k₄.mono hk2)).trans
      (k₅.mono hk2)).trans (k₆.mono hk2)).trans K'
  · rw [ladWM_eq] at U'
    refine (U₆.trans U').mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
        exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
    · rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
      · rw [List.mem_singleton.mp hw]; exact List.mem_append_right _ (List.mem_cons_self ..)
  · rw [Nat.shiftRight_zero] at R'
    exact R'

/-- `vg_<curve>_mul`: what its body gives (`mulBody_ok`), with `invKept` back
from the words past the table of bits; it changes only `invClob`'s registers. -/
theorem mulFn_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8) (hT : MulTmp c) (hL : LadLay c.mulLadder size) (hA : LadA c.mulLadder)
    (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hb3 : sv c base s BM = c.mont (3 * c.C.b))
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulFn s fun s' => KeepRegs (invClob c) s s' ∧ Unch base (mulWF c) s.mem s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hb4 := bitsAt0_le c h7
  have hl : c.invSaveLen = 8 * c.invKept.length := rfl
  have hk : c.invSaveLen ≤ 48 := by unfold Cfg.invSaveLen Cfg.invKept Cfg.invRegs; split <;> simp
  have hsz : c.mulSave + c.invSaveLen ≤ size := by unfold Cfg.mulSave; have : size = 8192 := rfl; omega
  have hsv8 : c.mulSave % 8 = 0 := by unfold Cfg.mulSave; have := bitsAt_mod8 c 0; omega
  rw [Cfg.mulFn]
  refine WP.seq (WP.mono (stAll_ok hs c.invKept (d := c.mulSave) (by omega) hsv8)
    fun s₁ ⟨k₁, g₁, O₁, S₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(c.mulSave, c.invSaveLen)] s.mem s₁.mem := by rw [hl]; exact O₁.unch
  have below : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ c.mulSave ∨ c.mulSave + c.invSaveLen ≤ c.sl i :=
      fun {i} hi => by
    by_cases hT : i = TMP
    · subst hT
      rcases h4 with h4 | h4 | h4
      · rw [sl_eq4 c (by omega), Cfg.mulSave, bitsAt_eq, h4]; left; simp only [TMP]; omega
      · rw [sl_tmp c (.inl h4), Cfg.mulSave, bitsAt_eq, h4]; right; simp only [Mont.moAt]; omega
      · rw [sl_tmp c (.inr (.inl h4)), Cfg.mulSave, bitsAt_eq, h4]; right; simp only [Mont.moAt]; omega
    · left
      have := Nat.mul_le_mul_left (8 * c.n) (show i + 1 ≤ 45 from hi)
      rw [sl_eq c i hT, Cfg.mulSave, bitsAt_eq, Nat.mul_succ] at *; omega
  have e₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi =>
    sv_unch U₁ h7 hn hi fun w hw => by
      rw [List.mem_singleton.mp hw]; exact below hi
  have q₁ : ptQ c base s₁ = ptQ c base s := by
    show Point.affine (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) = _
    rw [e₁ (by decide), e₁ (by decide)]
  refine WP.seq (WP.mono (mulBody_ok hc h4 hL hA hC hs₁ ((e₁ (by decide)).trans hmp)
    ((e₁ (by decide)).trans hz) ((e₁ (by decide)).trans hone) ((e₁ (by decide)).trans hap)
    ((e₁ (by decide)).trans hb3) (by rw [e₁ (by decide)]; exact hqx) (by rw [e₁ (by decide)]; exact hqy)
    (by rw [q₁]; exact hQ)) fun s₂ ⟨K₂, U₂, M₂, L₂, R₂⟩ => ?_)
  rw [q₁, e₁ (by decide)] at R₂
  have hs₂ := hs₁.of_keepRegs K₂ (x0_not_powClob h7)
  have S₂ : SavedAt s₂.mem base s.gpr c.mulSave c.invKept := SavedAt.congr S₁ fun e h₁ h₂ => by
    refine U₂.word (fun w hw => ?_) (by omega)
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hi45 : ∀ i ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ], i < 45 := by
        decide
      rcases below (hi45 i hi) with h | h
      · exact Or.inr (by dsimp only; omega)
      · exact Or.inl (by dsimp only; omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hT with h | h
        · rw [h]
          exact Or.inr (by
            unfold Cfg.mulSave at h₁
            rw [bitsAt_eq] at h₁
            simp only [slot, TMP]
            omega)
        · exact Or.inl (by dsimp only; omega)
      · exact Or.inr (by unfold Cfg.mulSave at *; dsimp only; omega)
  refine WP.mono (ldAll_ok hs₂ c.invKept (d := c.mulSave) (by omega) hsv8 (invKept_ne_x0 c))
    fun s₃ ⟨K₃, m₃, V₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [K₃.rd, K₂.rd, k₁.rd], by rw [K₃.wr, K₂.wr, k₁.wr],
    by rw [K₃.sp, K₂.sp, k₁.sp]⟩, ?_, by rw [m₃]; exact M₂, by rw [m₃]; exact L₂, ?_⟩
  · by_cases hkp : r ∈ c.invKept
    · exact V₃ s.gpr S₂ r hkp
    · have h19 : r ≠ .x19 := fun e => hkp (e ▸ List.mem_cons_self)
      have hcl : r ∉ clob c.n := fun h => hr (List.mem_filter.mpr ⟨h, by simpa using hkp⟩)
      rw [K₃.gpr _ hkp, K₂.gpr _ (by simp [powClob, h19, hcl]), k₁.gpr _ (by simp)]
  · rw [m₃]
    have hB : (bitsAt c.n 0, 64 * c.n + c.invSaveLen) ∈ mulWF c :=
      List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    have hI : (c.invTmp, 8 * c.n) ∈ mulWF c := List.mem_append_right _ (List.mem_cons_self ..)
    refine (U₁.trans U₂).cover fun w hw => ?_
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | hw | rfl | rfl
    · exact ⟨_, hB, by unfold Cfg.mulSave; omega, by unfold Cfg.mulSave; dsimp only; omega⟩
    · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hI, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, hB, Nat.le_refl _, by dsimp only; omega⟩
  · have e : ∀ x, tmv c.C c.n base s₃ x = tmv c.C c.n base s₂ x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [m₃]
    rw [e, e, e]; exact R₂

/-- What the call of a function that changes only `invClob`'s registers and
the ranges `W` needs and gives, from its caller's memory. -/
def fnK (c : Cfg) (base : Addr) (mem : Mem) (W : List (Nat × Nat)) (R : Mem → Mem → Prop) : Contract isa where
  pre t := Scr t base size ∧ t.mem = mem
  post t t' := KeepRegs (invClob c) t t' ∧ Unch base W t.mem t'.mem ∧ t'.v = t.v ∧ R t.mem t'.mem
  pub _ _ := True

/-- A call of the function `name`, whose code `fn` changes only `invClob`'s
registers (none of them callee-saved) and the ranges `W`, writes no vector
register, and gives `R`: as `fn` inline, keeping `x30` (in `v29`). -/
theorem fnCall_ok {name : String} {fn : Prog isa} {s : State} {base : Addr}
    (hs : Scr s base size) {W : List (Nat × Nat)} {R : Mem → Mem → Prop}
    (hfn : ∀ t, Scr t base size → t.mem = s.mem → WP isa fn t fun t' =>
      KeepRegs (invClob c) t t' ∧ Unch base W t.mem t'.mem ∧ R t.mem t'.mem)
    (hpres : ∀ r ∈ preserved, r ∉ clob c.n ∨ r ∈ c.invKept)
    (hv : fn.allInstrs (fun i => (vdstOf i).isNone) = true) (hnf : fn.noFrames = true) :
    WP isa (Cfg.invCall name fn) s fun s' => KeepRegs (powClob c.n) s s' ∧
      Unch base W s.mem s'.mem ∧ R s.mem s'.mem := by
  have hnv : ∀ (r : VReg), ∀ i ∈ instrs fn, vdstOf i ≠ some r := by
    intro r i hi e
    have := List.all_eq_true.mp ((Code.allInstrs_eq _ _) ▸ hv) i hi
    rw [e] at this; cases this
  rw [Cfg.invCall]
  refine WP.seq (WP.mono (keepLr_ok s) fun s₁ ⟨k₁, m₁, l₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hcov : Covers [⟨base, size⟩] s₁.wr := Covers.one ⟨_, hs₁.wr, by
    have := hs.contains (d := 0) (n := size) (by omega) (by decide)
    simpa [off] using this⟩
  refine WP.seq (WP.callV (k := fnK c base s.mem W R)
    (fun t ⟨ht, hm⟩ => by
      obtain ⟨tr, t', he, K, U, Rr⟩ := hfn t ht hm
      exact ⟨tr, t', he, ⟨fun r hr => K.gpr r fun h => (List.mem_filter.mp h).elim fun h₁ h₂ =>
          (hpres r hr).elim (· h₁) (by simpa using h₂), K.sp, Exec.preservedV he (by
        rw [Code.allInstrs_eq]; exact List.all_eq_true.mpr fun i hi => by
          unfold keepsV
          cases h : vdstOf i with
          | none => rfl
          | some r => exact absurd h (hnv r i hi))⟩, K, U, funext fun r => Exec.vec (hnv r) he, Rr⟩)
    (rd := []) (wr := [⟨base, size⟩]) ⟨⟨by
        rw [State.withRegions_gpr, State.callEntry_gpr _ (by decide), hs₁.x0], by simp,
        hs.nowrap, hs.enc⟩, by rw [State.withRegions_mem, State.callEntry_mem, m₁]⟩
      (Covers.right hcov) hcov ?_ hnf)
  intro s₂ r₂ w₂ p₂ _ _ _ _ ⟨K, U, V, Rr⟩
  simp only [State.withRegions_mem, State.callEntry_mem] at U Rr
  rw [m₁] at U Rr
  have V' : s₂.v = s₁.v := V
  refine WP.mono (Mont.lr_ok s₂) fun s₃ ⟨l₃, k₃⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [k₃.rd, r₂, k₁.rd], by rw [k₃.wr, w₂, k₁.wr], by rw [k₃.sp, p₂, k₁.sp]⟩,
    by rw [k₃.mem]; exact U, by rw [k₃.mem]; exact Rr⟩
  by_cases h30 : r = .x30
  · subst h30; rw [l₃, V', l₁]
  · simp only [powClob, List.mem_cons, not_or] at hr
    have h16 : Reg.x16 ∈ clob c.n := by simp [clob]
    have h17 : Reg.x17 ∈ clob c.n := by simp [clob]
    refine (k₃.gpr _ (by simpa using h30)).trans ((K.gpr r fun h => hr.2 (List.mem_filter.mp h).1).trans ?_)
    rw [State.withRegions_gpr, State.callEntry_gpr _ (by
      simp only [linkRegs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨fun e => hr.2 (e ▸ h16), fun e => hr.2 (e ▸ h17), h30⟩), k₁.gpr _ (by simp)]

/-- The constants but `b R`, kept, and `b R` written back. -/
theorem Fixed.unchBM {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Fixed c base g m)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 64) {W : List (Nat × Nat)} (hW : FixedOk c W)
    (hu : Unch base (slW c [BM] ++ W) m m') (hbm : wordsVal m' base (c.sl BM) c.n = c.mont c.C.b) :
    Fixed c base g m' := by
  have e : ∀ i, i < 12 → i ≠ TMP → i ≠ BM → wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n :=
    fun i hi hit hib => hu.wordsVal (apart_append (apart_slW (by simpa using hib)
      (by constructor <;> omega)) (fixed_apart hW hi hit))
      (by have := sl_le c h7 (i := i) (by omega); omega)
  refine ⟨(e MP (by decide) (by decide) (by decide)).trans h.mp,
    (e MN (by decide) (by decide) (by decide)).trans h.mn,
    (e ZERO (by decide) (by decide) (by decide)).trans h.zero,
    (e ONE (by decide) (by decide) (by decide)).trans h.one,
    (e ONEP (by decide) (by decide) (by decide)).trans h.onep,
    (e AP (by decide) (by decide) (by decide)).trans h.ap, hbm,
    (e GX (by decide) (by decide) (by decide)).trans h.gx,
    (e GY (by decide) (by decide) (by decide)).trans h.gy,
    (e R2N (by decide) (by decide) (by decide)).trans h.r2n,
    (e ONEN (by decide) (by decide) (by decide)).trans h.onen, fun p hp => ?_⟩
  have := setupSaved_lt p hp
  refine (hu.word (d := p.2) (fun w hw => Or.inl ?_) (by omega)).trans (h.saved p hp)
  rcases List.mem_append.mp hw with hw | hw
  · rw [List.mem_singleton.mp hw]; have := sl_ge64 c BM; dsimp only; omega
  · rcases hW w hw with ⟨h1, -⟩ | h
    · rw [h1]; simp only [slot]; omega
    · simp (disch := decide) only [sl_eq] at h; omega

/-- A slot apart from what the function writes. -/
theorem apart_mulWF (hT : MulTmp c) {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP])
    (hiA : i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82 := by first | decide | exact ⟨by omega, by omega⟩) :
    ∀ w ∈ mulWF c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  have hT' : i ≠ TMP := fun h => hl (by simp [h])
  refine apart_append (apart_slW (fun h => hl (List.mem_append_left [TMP] h)) hiA) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rcases hT with h | h
    · dsimp only; rw [h]; exact sl_apart_raw_tmp c hT'
    · exact Or.inl (by have := sl_below_bits c hi 0 0 hT'; unfold Cfg.mulSave at h; dsimp only; omega)
  · exact Or.inl (by have := sl_below_bits c hi 0 0 hT'; dsimp only; omega)

/-- The flag's word, apart from what the function and the slots `l` write. -/
theorem flag_unch_mulWF (hT : MulTmp c) {base : Addr} {l : List Nat} {m m' : Mem} (hu : Unch base (slW c l ++ mulWF c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) (hl : FLAG ∉ l)
    (hlA : ∀ j ∈ l, j ≠ 54 ∧ j ≠ 61 ∧ j ≠ 82 := by decide) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_append (apart_slW hl (by decide) hlA) (apart_mulWF (c := c) hT (i := FLAG) (by decide) (by decide)) w hw with
    h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem fixedOk_mulWF (hT : MulTmp c) : FixedOk c (mulWF c) := by
  refine (fixedOk_slW (by decide)).append fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rcases hT with h | h
    · exact Or.inl ⟨h, rfl⟩
    · exact Or.inr (by have := sl_below_bits c (i := 12) (by decide) 0 0; unfold Cfg.mulSave at h; dsimp only; omega)
  · exact Or.inr (by have := sl_below_bits c (i := 12) (by decide) 0 0; dsimp only; omega)

/-- `R = [k]P`, for the `k` in `K`'s slot and the affine point `P` on the curve
at `px` and `py`, by a call of `vg_<curve>_mul`: `P` copied to `R`'s first two
slots and `3 b R` to `BM`'s slot, then `b R` back; the constants are kept. -/
theorem mulAt_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8) (hT : MulTmp c) (hL : LadLay c.mulLadder size) (hA : LadA c.mulLadder)
    (hC : Law c.C) (hv : c.mulFn.allInstrs (fun i => (vdstOf i).isNone) = true)
    (hnf : c.mulFn.noFrames = true) {name : String} {px py : Nat}
    (hpx45 : px < 45) (hpy45 : py < 45) (hpxl : px ∉ [RX, RY, BM, TMP]) (hpyl : py ∉ [RX, RY, BM, TMP])
    (hpyA : py ≠ 54 ∧ py ≠ 61 ∧ py ≠ 82)
    {base : Addr} {g : Reg → BitVec 64} {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem)
    (hpx : sv c base s px < c.C.p) (hpy : sv c base s py < c.C.p)
    (hP : onCurve c.C (.affine (tmv c.C c.n base s (c.sl px)) (tmv c.C c.n base s (c.sl py))) = true) :
    WP isa (c.mulAt name px py) s fun s' => KeepRegs (powClob c.n) s s' ∧
      Unch base (slW c [BM] ++ mulWF c) s.mem s'.mem ∧ Fixed c base g s'.mem ∧
      ModOkA c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ))
        (mul (sv c base s K) (.affine (tmv c.C c.n base s (c.sl px)) (tmv c.C c.n base s (c.sl py)))) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
  have m8 := sl_mod8 c
  have ap : ∀ {i j}, i ≠ j → i ≠ TMP → j ≠ TMP → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i :=
    fun h hi hj => by rcases sl_apart c h (.inl hi) (.inl hj) with h | h <;> omega
  rw [Cfg.mulAt]
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) c.n hs (o := c.sl RX) (a := c.sl px)
    (sz (by decide)) (sz hpx45) (m8 _) (m8 _) (ap (by simp at hpxl; omega) (by decide) (by simp at hpxl; omega))) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl RY) (a := c.sl py)
    (sz (by decide)) (sz hpy45) (m8 _) (m8 _) (ap (by simp at hpyl; omega) (by decide) (by simp at hpyl; omega))) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (setConst_ok hs₂ (n := c.n) (o := c.sl BM) (x := c.mont (3 * c.C.b))
    (sz (by decide)) (m8 _) (lt_trans (hmont _) hc.p_lt)) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  have U₃ : Unch base (slW c [RX, RY, BM]) s.mem s₃.mem :=
    ((O₁.unch.trans O₂.unch).trans O₃.unch).mono fun w hw => by simpa [or_assoc] using hw
  have O₁' : Unch base (slW c [RX]) s.mem s₁.mem := O₁.unch
  have O₂' : Unch base (slW c [RY]) s₁.mem s₂.mem := O₂.unch
  have O₃' : Unch base (slW c [BM]) s₂.mem s₃.mem := O₃.unch
  have e₃ : ∀ {i}, i < 45 → i ∉ [RX, RY, BM] → sv c base s₃ i = sv c base s i := fun hi hl =>
    sv_unch U₃ h7 hn hi (apart_slW hl)
  have rx₃ : sv c base s₃ RX = sv c base s px :=
    (sv_unch (O₂'.trans O₃') h7 hn (i := RX) (by decide)
      (apart_append (apart_slW (by decide)) (apart_slW (by decide)))).trans v₁
  have px₁ : sv c base s₁ py = sv c base s py :=
    sv_unch O₁' h7 hn hpy45 (apart_slW (by simp at hpyl ⊢; omega) hpyA)
  have ry₃ : sv c base s₃ RY = sv c base s py :=
    ((sv_unch O₃' h7 hn (i := RY) (by decide) (apart_slW (by decide))).trans v₂).trans px₁
  have hq₃ : ptQ c base s₃ = .affine (tmv c.C c.n base s (c.sl px)) (tmv c.C c.n base s (c.sl py)) := by
    show Point.affine (toM _ _ (sv c base s₃ RX)) (toM _ _ (sv c base s₃ RY)) = _
    rw [rx₃, ry₃]
  have k₃' : sv c base s₃ K = sv c base s K := e₃ (by decide) (by decide)
  -- The call.
  let Rr : Mem → Mem → Prop := fun _ m' => ModOkA c.MP' size c.C.p m' base ∧
    (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal m' base x c.n < c.C.p) ∧
    Rep c.C (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl RX) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl RY) c.n))
      (toM c.C.p (2 ^ (64 * c.n)) (wordsVal m' base (c.sl RZ) c.n))
      (mul (sv c base s K) (.affine (tmv c.C c.n base s (c.sl px)) (tmv c.C c.n base s (c.sl py))))
  have hpres : ∀ r ∈ preserved, r ∉ clob c.n ∨ r ∈ c.invKept := by
    unfold Cfg.invKept Cfg.invRegs; rcases h4 with h4 | h4 | h4 <;> rw [h4] <;> decide
  refine WP.seq (WP.mono (fnCall_ok (name := name) (W := mulWF c) (R := Rr) hs₃ (fun t ht hm => ?_) hpres hv hnf)
    fun s₄ ⟨K₄, U₄, R₄⟩ => ?_)
  · have et : ∀ i, sv c base t i = sv c base s₃ i := fun i => by
      show wordsVal t.mem _ _ _ = wordsVal s₃.mem _ _ _; rw [hm]
    have hqt : ptQ c base t = ptQ c base s₃ := by
      show Point.affine (toM _ _ (sv c base t RX)) (toM _ _ (sv c base t RY)) = _
      rw [et, et]
    refine WP.mono (mulFn_ok hc h4 hT hL hA hC ht
      (by rw [et, e₃ (by decide) (by decide)]; exact F.mp)
      (by rw [et, e₃ (by decide) (by decide)]; exact F.zero)
      (by rw [et, e₃ (by decide) (by decide)]; exact F.onep)
      (by rw [et, e₃ (by decide) (by decide)]; exact F.ap)
      (by rw [et]; exact b₃)
      (by rw [et, rx₃]; exact hpx) (by rw [et, ry₃]; exact hpy)
      (by rw [hqt, hq₃]; exact hP)) fun t' ⟨K', U', M', L', R'⟩ => ⟨K', U', M', L', ?_⟩
    rw [hqt, hq₃, et, k₃'] at R'
    exact R'
  have hs₄ := hs₃.of_keepRegs K₄ (x0_not_powClob h7)
  obtain ⟨M₄, L₄, R₄⟩ := R₄
  refine WP.mono (setConst_ok hs₄ (n := c.n) (o := c.sl BM) (x := c.mont c.C.b)
    (sz (by decide)) (m8 _) (lt_trans (hmont _) hc.p_lt)) fun s₅ ⟨b₅, k₅, O₅⟩ => ?_
  have O₅' : Unch base (slW c [BM]) s₄.mem s₅.mem := O₅.unch
  have U₅ : Unch base (slW c [BM] ++ mulWF c) s.mem s₅.mem :=
    ((U₃.trans U₄).trans O₅').mono fun w hw => by
      simp only [List.mem_append] at hw ⊢
      rcases hw with (hw | hw) | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · exact .inr (.inl (List.mem_map_of_mem (by decide)))
        · exact .inr (.inl (List.mem_map_of_mem (by decide)))
        · exact .inl (List.mem_singleton_self _)
      · exact .inr hw
      · exact .inl hw
  have F₅ : Fixed c base g s₅.mem := F.unchBM h7 hn (fixedOk_mulWF hT) U₅ b₅
  have r₅ : ∀ {i}, i < 45 → i ≠ BM → sv c base s₅ i = sv c base s₄ i := fun hi hb =>
    sv_unch O₅' h7 hn hi (apart_slW (by simpa using hb))
  have hk : ∀ r ∈ [Reg.x1], r ∈ powClob c.n := fun r hr => by
    simp only [List.mem_singleton] at hr; simp [hr, powClob, clob]
  refine ⟨(((k₁.mono hk).trans (k₂.mono hk)).trans (k₃.mono hk)).trans (K₄.trans (k₅.mono hk)), U₅, F₅,
    modP_of hc F₅.mp, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · rw [show wordsVal s₅.mem base (c.sl RX) c.n = sv c base s₅ RX from rfl, r₅ (by decide) (by decide)]
      exact L₄ _ (by simp)
    · rw [show wordsVal s₅.mem base (c.sl RY) c.n = sv c base s₅ RY from rfl, r₅ (by decide) (by decide)]
      exact L₄ _ (by simp)
    · rw [show wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s₅ RZ from rfl, r₅ (by decide) (by decide)]
      exact L₄ _ (by simp)
  · show Rep c.C (toM _ _ (sv c base s₅ RX)) (toM _ _ (sv c base s₅ RY)) (toM _ _ (sv c base s₅ RZ)) _
    rw [r₅ (by decide) (by decide), r₅ (by decide) (by decide), r₅ (by decide) (by decide)]
    exact R₄

end VG.Proof.Ecdsa.AArch64
