module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays

/-!
# `vg_<curve>_mul` on x86-64, and `R = [k]G` by its call

`Cfg.mulBody`: the table of `k`'s bits (`bits_ok`), from the scalar in `K`'s
slot, `Q` (in `R`'s first two slots) copied to `ACC` and `PT`, `R` the point
at infinity (copies of zero and one, `copy_ok`), then `R = [k]Q` by the
ladder (`ladder_ok`, `step_rep'`, with the formulas for `a = 0` if the curve's `a`
is zero), which reads `p`, `a R` and `3 b R` from
their slots and writes only its slots, `R`'s, `ACC`'s, `PT`'s and the table
of bits (`mulBody_ok`). `Cfg.mulFn` runs it between copying the callee-saved
registers to `xmm0`–`xmm5` and back (`mulFn_ok`), as the inversions do; that
they come back is a fact of runs (`invFnX_gpr`). `gMulKC_ok`: `R = [k]G` in
the signature and the public key, by a call of `vg_<curve>_mul_base` or of
`vg_<curve>_mul` (with `G` copied to `R`'s slots), or inline.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `vg_<curve>_mul`'s body writes: `R`'s slots, `ACC`'s and `PT`'s (its
copy of `Q`), the ladder's and the table of `k`'s bits. -/
abbrev mulW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
    [(bitsAt c.n 0, 64 * c.n + 8)]

/-- The point `Q` in `R`'s first two slots, as the proofs decode it. -/
abbrev ptQ (c : Cfg) (base : Addr) (s : State) : Point c.C :=
  .affine (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))

theorem ladLayM (hc : BaseCfgOk c) : LadLay c.mulLadder size := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, B3P, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, B3P, DX, DY, DZ, ACC, PT, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn (i := RX) (j := RY) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RX) (j := RZ) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RY) (j := RZ) h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega_arith, show 64 * c.n < 2 ^ 16 by omega_arith⟩, bitsAt_le c h7 (by decide), ?_⟩
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
      exact Or.inr (sl_below_bits c (hl i hi) 0 0 (.inl fun h => by subst h; exact absurd hi (by decide)))
    · rcases tmp_apart_bits c (j := 0) (.inl (by decide)) (by decide) (64 * c.n) (by omega_arith) with h | h
      · exact Or.inr (by show c.sl TMP + 8 * c.n ≤ bitsAt c.n 0; exact h)
      · exact Or.inl (by show bitsAt c.n 0 + 64 * c.n ≤ c.sl TMP; exact h)

theorem ladWM_eq (c : Cfg) : ladW c.mulLadder = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] := rfl

/-- A slot apart from the table of bits and from the slots `l`. -/
theorem apart_bits_slW {i : Nat} (hi : i < 45) {l : List Nat} (hl : i ∉ l) :
    ∀ w ∈ [(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_pad hi) (apart_slW hl)

/-- `R = [k]Q` for the `k` in `K`'s slot and the point `Q` on the curve in
`R`'s first two slots, with the table of `k`'s bits, from `p`, zero, one,
`a R` and `3 b R` in their slots. -/
theorem mulBody_ok (hc : BaseCfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hb3 : sv c base s B3P = c.mont (3 * c.C.b))
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulBody.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (mulW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  have sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
  have ap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    rcases sl_apart c h with h | h <;> omega_arith
  show WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl PT) (c.sl RY) ++
      copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO)))
      (ladder c.mulLadder (c.C.a == 0)).inline)) s _
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (by omega_arith) (sz (i := K) (by decide)) hsz
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0 (.inl (by decide)); omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n + 8)] s.mem s₁.mem := fun x hx =>
    O₁ x (by have := hx _ (List.mem_singleton_self _); dsimp only at this; omega_arith)
  -- `Q` to `ACC` and `PT`, and `R` the point at infinity.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl ACC) (a := c.sl RX)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₂ (o := c.sl PT) (a := c.sl RY)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₃ (o := c.sl RX) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₄ ⟨v₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₄ (o := c.sl RY) (a := c.sl ONEP)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₅ ⟨v₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₅ (o := c.sl RZ) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- What each copy leaves.
  have U₂ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC]) s.mem s₂.mem := U₁.trans O₂.unch
  have U₃ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT]) s.mem s₃.mem := U₂.trans O₃.unch
  have U₄ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX]) s.mem s₄.mem :=
    U₃.trans O₄.unch
  have U₅ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY]) s.mem s₅.mem :=
    U₄.trans O₅.unch
  have U₆ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY, RZ]) s.mem s₆.mem :=
    U₅.trans O₆.unch
  have U₂₆ : Unch base (slW c [PT, RX, RY, RZ]) s₂.mem s₆.mem :=
    ((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch
  have U₃₆ : Unch base (slW c [RX, RY, RZ]) s₃.mem s₆.mem := (O₄.unch.trans O₅.unch).trans O₆.unch
  have U₄₆ : Unch base (slW c [RY, RZ]) s₄.mem s₆.mem := O₅.unch.trans O₆.unch
  have U₅₆ : Unch base (slW c [RZ]) s₅.mem s₆.mem := O₆.unch
  have e₁ := fun {i} (hi : i < 45) => sv_unch U₁ h7 hn hi (apart_pad hi)
  have acc₆ : sv c base s₆ ACC = sv c base s RX :=
    (sv_unch U₂₆ h7 hn (i := ACC) (by decide) (apart_slW (by decide))).trans (v₂.trans (e₁ (by decide)))
  have pt₆ : sv c base s₆ PT = sv c base s RY :=
    (sv_unch U₃₆ h7 hn (i := PT) (by decide) (apart_slW (by decide))).trans
      (v₃.trans (sv_unch U₂ h7 hn (i := RY) (by decide) (apart_bits_slW (by decide) (by decide))))
  have rx₆ : sv c base s₆ RX = 0 :=
    (sv_unch U₄₆ h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans
      (v₄.trans ((sv_unch U₃ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz))
  have one₄ : sv c base s₄ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (sv_unch U₄ h7 hn (i := ONEP) (by decide) (apart_bits_slW (by decide) (by decide))).trans hone
  have ry₆ : sv c base s₆ RY = c.mont 1 := by
    have h := (sv_unch U₅₆ h7 hn (i := RY) (by decide) (apart_slW (by decide))).trans (v₅.trans one₄)
    rw [show c.mont 1 = 2 ^ (64 * c.n) % c.C.p by show 1 * c.R % c.C.p = _; rw [Nat.one_mul]; rfl]
    exact h
  have rz₆ : sv c base s₆ RZ = 0 :=
    v₆.trans ((sv_unch U₅ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz)
  have e₆ := fun {i} (hi : i < 45) (hl : i ∉ [ACC, PT, RX, RY, RZ]) =>
    sv_unch U₆ h7 hn hi (apart_bits_slW hi hl)
  have mp₆ : sv c base s₆ MP = c.C.p := (e₆ (i := MP) (by decide) (by decide)).trans hmp
  have ap₆ : sv c base s₆ AP = c.mont c.C.a := (e₆ (i := AP) (by decide) (by decide)).trans hap
  have b3₆ : sv c base s₆ B3P = c.mont (3 * c.C.b) := (e₆ (i := B3P) (by decide) (by decide)).trans hb3
  have one₆ : sv c base s₆ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (e₆ (i := ONEP) (by decide) (by decide)).trans hone
  have U₂₆' : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem :=
    ((((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch)
  have k₆' : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch U₂₆' h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t ht)]
    exact b₁ t ht
  -- The ladder.
  have hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, ACC, PT, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₆ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt ap₆ (hmont _)
    · exact lt_of_eq_of_lt b3₆ (hmont _)
    · rw [acc₆]; exact hqx
    · rw [pt₆]; exact hqy
    · exact lt_of_eq_of_lt one₆ (Nat.mod_lt _ (by omega_arith))
    · exact lt_of_eq_of_lt rx₆ (by omega_arith)
    · exact lt_of_eq_of_lt ry₆ (hmont _)
    · exact lt_of_eq_of_lt rz₆ (by omega_arith)
  have hG : Rep c.C (tmv c.C c.n base s₆ (c.sl ACC)) (tmv c.C c.n base s₆ (c.sl PT))
      (tmv c.C c.n base s₆ (c.sl ONEP)) (ptQ c base s) := by
    show Rep c.C (toM _ _ (sv c base s₆ ACC)) (toM _ _ (sv c base s₆ PT)) (toM _ _ (sv c base s₆ ONEP))
      (Point.affine (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)))
    rw [acc₆, pt₆, one₆, toM_one hpR]
    exact rep_affine' hC _ _
  have hstep := step_rep' (L := c.mulLadder) (k := sv c base s K) (a0 := c.C.a == 0) hC hQ
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ AP) = _; rw [ap₆]; exact toM_cmont hc _)
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ B3P) = _; rw [b3₆]; exact toM_cmont hc _) hG
    fun h0 => ⟨by rw [beq_iff_eq.mp h0]; rfl, by
      show toM _ _ (sv c base s₆ ONEP) = 1; rw [one₆]; exact toM_one hpR⟩
  have hR : Rep c.C (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY))
      (tmv c.C c.n base s₆ (c.sl RZ)) (mul (sv c base s K >>> (64 * c.n)) (ptQ c base s)) := by
    show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [rx₆, ry₆, rz₆, toM_cmont hc, toM_zero, shiftRight_eq_zero (wordsVal_lt _ _ _ _), mul_zero_pt]
    exact rep_infinity' hC
  have hk1 : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  have hk2 : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => hk1 r (by
    simp only [List.mem_singleton] at hr; simp [hr])
  refine WP.mono (ladder_ok (ladLayM hc) hpR hs₆ (modP_of hc mp₆) hlt hstep hR k₆')
    fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, ?_, M', L', ?_⟩
  · exact ((((((k₁.mono hk1).trans (k₂.mono hk2)).trans (k₃.mono hk2)).trans (k₄.mono hk2)).trans
      (k₅.mono hk2)).trans (k₆.mono hk2)).trans K'
  · rw [ladWM_eq] at U'
    have hsub : ∀ w ∈ ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY, RZ]) ++
        slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP],
        w ∈ mulW c := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_right _ hw
        · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
      · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
    exact Unch.cover (U₆.trans U') fun w hw => ⟨w, hsub w hw, Nat.le_refl _, Nat.le_refl _⟩
  · rw [Nat.shiftRight_zero] at R'
    exact R'

/-- `vg_<curve>_mul`, for a curve of four or six words: what its body gives
(`mulBody_ok`); the registers it copies to `xmm` registers and back are
among those its body changes (`powClob`). -/
theorem mulFn_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8) (hC : Law c.C) {base : Addr} {s : State}
    (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a) (hb3 : sv c base s B3P = c.mont (3 * c.C.b))
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulFn.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (mulW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  have hkept : ∀ r ∈ Cfg.invKeptX.map Prod.fst, r ∈ powClob c.n := by
    rcases h4 with h | h | h <;> rw [h] <;> decide
  show WP isa (.seq (.block _) (.seq c.mulBody.inline (.block _))) s _
  refine WP.seq (WP.mono (savesX_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  have ev : ∀ i, sv c base s₁ i = sv c base s i := fun i => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  have eQ : ptQ c base s₁ = ptQ c base s := by
    show Point.affine (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) = _
    rw [ev, ev]
  refine WP.seq (WP.mono (mulBody_ok hc hC hs₁ ((ev _).trans hmp) ((ev _).trans hz)
    ((ev _).trans hone) ((ev _).trans hap) ((ev _).trans hb3) (by rw [ev]; exact hqx)
    (by rw [ev]; exact hqy) (by rw [eQ]; exact hQ)) fun s₂ ⟨K₂, U₂, M₂, L₂, R₂⟩ => ?_)
  rw [ev, eQ] at R₂
  refine WP.mono (restoresX_ok s₂) fun s' ⟨g', m', rd', wr'⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [g' r (fun h => hr (hkept r h)), K₂.gpr r hr, g₁]
  · rw [rd', K₂.rd, rd₁]
  · rw [wr', K₂.wr, wr₁]
  · rw [m', ← m₁]; exact U₂
  · rw [m']; exact M₂
  · rw [m']; exact L₂
  · have e : ∀ x, tmv c.C c.n base s' x = tmv c.C c.n base s₂ x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [m']
    rw [e, e, e]; exact R₂

/-- What the copies of `G` and `vg_<curve>_mul` write is in what `gMulKC` may
write. -/
theorem mulW_sub :
    ∀ w ∈ slW c [RX, RY] ++ mulW c, ∃ w' ∈ gWA c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  have hA : ACC ∈ c.mulBaseSlots := by unfold Cfg.mulBaseSlots; split <;> simp
  intro w hw
  refine ⟨w, ?_, Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact List.mem_append_left _ (List.mem_append_left _ (List.map_subset _ (by decide) hw))
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have key : ∀ i ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
          i = ACC ∨ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by
        decide
      rcases key i hi with rfl | h
      · exact List.mem_append_right _ (List.mem_map_of_mem hA)
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h))
    · exact List.mem_append_left _ (List.mem_append_right _ hw)

/-- `R = [k]G` for a secret `k`, after the setup and the tables (but `k`'s
if `vg_<curve>_mul_base` or `vg_<curve>_mul` makes it): by their calls, or
inline (`gMulK_ok`). -/
theorem gMulKC_ok (hc : BaseCfgOk c) (hmb : MulBaseOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat}
    {s₀ : State} (hp : Pre c s₀) {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s c.callsMul) :
    WP isa c.gMulKC.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) := by
  unfold Cfg.gMulKC
  cases hm : c.mulBase with
  | some C =>
    obtain ⟨d, hcd, h3, hnc⟩ := hmb.1 (by rw [hm]; rfl)
    obtain ⟨hTM, hout⟩ := tbl_of hcd hp hS.rd hS.unch
    rw [← hS.syms] at hTM hout
    show WP isa c.mulBaseFn s _
    rw [← Code.inline_of_noCalls hnc]
    refine WP.mono (mulBaseFn_ok hc h3 hC hT hcd hS.scr hS.fixed.mp hS.fixed.zero hTM hout)
      fun s' ⟨g', _, rd', wr', _, U', M', L', R'⟩ => ⟨⟨g', rd', wr'⟩, U', M', L', ?_⟩
    rw [← hS.k]; exact R'
  | none =>
    cases hm₂ : c.mul with
    | none =>
      rw [show c.callsMul = false by simp [Cfg.callsMul, hm, hm₂]] at hS
      exact WP.mono (gMulK_ok hc hC hT hp hS) fun s' ⟨K', U', M', L', R'⟩ =>
        ⟨K', U'.mono fun w hw => List.mem_append_left _ hw, M', L', R'⟩
    | some C =>
      obtain ⟨h4, hnc⟩ := hmb.2 (by rw [hm₂]; rfl)
      have F := hS.fixed
      have hs := hS.scr
      have h7 := hc.n10
      have hn := hs.nowrap
      have hp3 := hc.p_ge
      have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
      have sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
      show WP isa (.seq (.block (copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY))) c.mulFn) s _
      rw [← Code.inline_of_noCalls hnc]
      refine WP.seq ?_
      rw [WP.block_append_iff]
      refine WP.mono (copy_ok (size := size) c.n hs (o := c.sl RX) (a := c.sl GX)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RX) (j := GX) (by decide) with h | h <;> omega_arith))
        fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
      have hs₁ := hs.of_keepRegs k₁ (by decide)
      refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl RY) (a := c.sl GY)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RY) (j := GY) (by decide) with h | h <;> omega_arith))
        fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
      have hs₂ := hs₁.of_keepRegs k₂ (by decide)
      have U₂ : Unch (s₀.gpr .r8) (slW c [RX, RY]) s.mem s₂.mem := O₁.unch.trans O₂.unch
      have e₂ := fun {i} (hi : i < 45) (hl : i ∉ [RX, RY]) => sv_unch U₂ h7 hn hi (apart_slW hl)
      have O₁' : Unch (s₀.gpr .r8) (slW c [RX]) s.mem s₁.mem := O₁.unch
      have O₂' : Unch (s₀.gpr .r8) (slW c [RY]) s₁.mem s₂.mem := O₂.unch
      have rx₂ : sv c (s₀.gpr .r8) s₂ RX = c.mont c.C.gx :=
        (sv_unch O₂' h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans (v₁.trans F.gx)
      have ry₂ : sv c (s₀.gpr .r8) s₂ RY = c.mont c.C.gy :=
        v₂.trans ((sv_unch O₁' h7 hn (i := GY) (by decide) (apart_slW (by decide))).trans F.gy)
      have eG : ptQ c (s₀.gpr .r8) s₂ = G c.C := by
        show Point.affine (toM _ _ (sv c _ s₂ RX)) (toM _ _ (sv c _ s₂ RY)) = Point.affine _ _
        rw [rx₂, ry₂, toM_cmont hc, toM_cmont hc]
      refine WP.mono (mulFn_ok hc h4 hC hs₂ ((e₂ (by decide) (by decide)).trans F.mp)
        ((e₂ (by decide) (by decide)).trans F.zero) ((e₂ (by decide) (by decide)).trans F.onep)
        ((e₂ (by decide) (by decide)).trans F.ap) ((e₂ (by decide) (by decide)).trans F.b3p)
        (lt_of_eq_of_lt rx₂ (hmont _)) (lt_of_eq_of_lt ry₂ (hmont _)) (by rw [eG]; exact hc.onG))
        fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, Unch.cover (U₂.trans U') mulW_sub, M', L', ?_⟩
      · have hk : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => by
          simp only [List.mem_singleton] at hr; simp [hr, powClob, clob]
        exact ((k₁.mono hk).trans (k₂.mono hk)).trans K'
      · have k₂ : sv c (s₀.gpr .r8) s₂ K = sv c (s₀.gpr .r8) s K := e₂ (by decide) (by decide)
        rw [eG, k₂, hS.k] at R'; exact R'

end VG.Proof.Ecdsa.X86_64
