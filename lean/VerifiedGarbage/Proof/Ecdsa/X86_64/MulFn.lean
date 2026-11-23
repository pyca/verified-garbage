module

import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Weierstrass.X86_64.NafState
import VerifiedGarbage.Proof.Weierstrass.X86_64.JacState
import VerifiedGarbage.Proof.Weierstrass.X86_64.Unch
import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law

/-! ### `Ecdsa.X86_64.MulBase`, which this module and modules that import it used -/

section

/-! ### `Ecdsa.X86_64.GMul`, which this module and modules that import it used -/

section

/-! ### `Weierstrass.X86_64.Rep`, which this module and modules that import it used -/

section

/-!
# Short Weierstrass curves on x86-64: the ladder computes `[k]P`

The invariant of the group law for `ladder_ok`: `R` represents `[k >>> j]P`,
for the point `P` that `G` represents, which an iteration keeps
(`step_rep`, by `ladder_step`) when the slots of `a` and `3b` hold the
curve's, and with the formulas for `a = 0` (`step_rep'`) when the curve's `a`
is zero and `G`'s `Z` one.
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass Spec.Weierstrass

theorem step_rep' {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P)
    {a0 : Bool} (h0 : a0 = true → (Fin.ofNat C.p C.a : Fe C) = 0 ∧ tmv C L.M.n base s L.G.z = 1) :
    Step L C base s k (fun j X Y Z => Rep C X Y Z (mul (k >>> j) P)) a0 := by
  intro j _ X Y Z X2 Y2 Z2 X3 Y3 Z3 hQ h2 h3
  rw [ha, hb] at h2 h3
  exact ladder_step' hC hP h0 hG hQ h2 h3

theorem step_rep {L : LadderCfg} {C : Curve} {base : Addr} {s : State} {k : Nat} {P : Point C}
    (hC : Law C) (hP : onCurve C P = true)
    (ha : tmv C L.M.n base s L.S.a = Fin.ofNat C.p C.a)
    (hb : tmv C L.M.n base s L.S.b3 = Fin.ofNat C.p (3 * C.b))
    (hG : Rep C (tmv C L.M.n base s L.G.x) (tmv C L.M.n base s L.G.y) (tmv C L.M.n base s L.G.z) P) :
    Step L C base s k fun j X Y Z => Rep C X Y Z (mul (k >>> j) P) :=
  step_rep' hC hP ha hb hG nofun

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# ECDSA on x86-64: `[k]G`

`Cfg.gMul` is the comb for a curve with one, else the ladder (`Cfg.gMulK`, for a
secret scalar, the comb with Booth's digits where the curve's has them); each leaves
`R = [k]G`, from the table of `k`'s bits, changing only the slots and word of
`gW` (`gMul_ok'`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What `[k]G` may write, by the comb (with `b R mod p` in `EM`) or the
ladder, or by `vg_<curve>_mul_base`, which also makes the table of `k`'s
bits: their slots, and that table with the word past it. -/
abbrev gW (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] ++
    [(bitsAt c.n 0, 64 * c.n + 8)]

/-- A slot is apart from the table of `k`'s bits and the word past it. -/
theorem apart_pad {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 0, 64 * c.n + 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact sl_apart_bits c hi (j := 0) (.inr (.inl (by decide))) (64 * c.n + 8) (by omega_using [])

/-- A slot apart from what `[k]G` writes. -/
theorem apart_gW {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]) :
    ∀ w ∈ gW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_pad hi)

theorem fixedOk_gW : FixedOk c (gW c) := by
  refine FixedOk.append (fixedOk_slW (by decide)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 0 _))

/-- Tables `1` and `2` are apart from what `[k]G` writes. -/
theorem tbl_apart_gW {j t : Nat} (hj : j = 1 ∨ j = 2) (ht : t < 64 * c.n)
    (hj1 : j ≠ 1 ∨ c.n ≠ 9 := by sl_or) :
    ∀ w ∈ gW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW (by decide) j t ht (.inr hj1)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  rcases hj with rfl | rfl <;> exact Or.inr (by omega_using [])

/-- `R = [k]G` by a comb `P` (`d`'s, with its tables where it reads them),
after `b R mod p` is put in `EM`: what `P` gives from `TCombFixed`, `gMul`'s
postcondition. -/
theorem gMulComb_ok' (hc : BaseCfgOk c) {d : CombData} (hcd : c.comb = some d) {base : Addr}
    {s : State} (hs : Scr s base size) (hmp : wordsVal s.mem base (c.sl MP) c.n = c.C.p)
    (hz : wordsVal s.mem base (c.sl ZERO) c.n = 0) {k : Nat}
    (hkl : k < 2 ^ (64 * c.n))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) {P : Prog isa}
    (hP : ∀ s₁, Scr s₁ base size → ModOkW (c.combCfg d).M size c.C.p s₁.mem base →
      TCombFixed (c.combCfg d) c.C base size s₁ k (s₁.syms d.tsym)
        (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) →
      WP isa P s₁ fun s' => KeepRegs (powClob (c.combCfg d).M.n) s₁ s' ∧
        Unch base (tcombW (c.combCfg d)) s₁.mem s'.mem ∧ ModOkW (c.combCfg d).M size c.C.p s'.mem base ∧
        (∀ x ∈ [(c.combCfg d).A.x, (c.combCfg d).A.y, (c.combCfg d).A.z],
          wordsVal s'.mem base x (c.combCfg d).M.n < c.C.p) ∧
        Rep c.C (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.x)
          (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.y)
          (tmv c.C (c.combCfg d).M.n base s' (c.combCfg d).A.z) (mul k (G c.C))) :
    WP isa (.seq (.block (setConst c.n (c.sl EM) (c.mont c.C.b))) P) s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hp3])
  have hd := hc.comb d hcd
  have hn := hs.nowrap
  -- `b R mod p` in `EM`.
  refine WP.seq (WP.mono_syms (setConst_ok hs (n := c.n) (o := c.sl EM) (x := c.mont c.C.b)
    (sl_le c h7 (by decide)) (by have := hc.p_lt; have := hmont c.C.b; omega_arith))
    fun s₁ ⟨e₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch O₁.unch h7 hn (i := MP) (by decide) (apart_slW (l := [EM]) (by decide))).trans hmp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch O₁.unch h7 hn (i := ZERO) (by decide) (apart_slW (l := [EM]) (by decide))).trans hz
  have ht₁ : ∀ t < 64 * c.n, s₁.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0 :=
    fun t ht => by
      rw [tbl_unch (W := slW c [EM]) O₁.unch h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t ht)]
      exact ht₀ t ht
  have hTM₁ : TblMem s₁ (s.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.rd, k₁.wr]) O₁.unch (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact sl_le c h7 (by decide)) hout
  have hF : TCombFixed (c.combCfg d) c.C base size s₁ k (s₁.syms d.tsym)
      (tcombWords (c.combCfg d).M.n (2 ^ (64 * (c.combCfg d).M.n)) c.C.p d.tbl) := by
    refine ⟨?_, fun x hx => ?_, hz₁, ht₁, hkl, rfl, by rw [sy₁]; exact hTM₁,
      by rw [sy₁]; exact hout⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem _ (c.sl EM) c.n) = _
      rw [e₁]; exact toM_cmont hc _
    · simp only [combRo, TCombCfg.toComb, Cfg.combCfg, Cfg.rcbSlots, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt e₁ (hmont _)
      · exact lt_of_eq_of_lt e₁ (hmont _)
      · exact lt_of_eq_of_lt hz₁ (by omega_using [hp3])
  refine WP.mono (hP s₁ hs₁ ((modP_of hc hmp₁).inl c.hot) hF) fun s' ⟨K', U', M', L', R'⟩ =>
      ⟨(k₁.mono fun r hr => by rw [List.mem_singleton.mp hr]; simp [powClob, clob]).trans K', ?_, M'.of_inl, L', R'⟩
  rw [tcombW_eq] at U'
  have hz := zw_le hd
  refine Unch.cover (O₁.unch.trans U') fun w hw => ?_
  rcases List.mem_append.mp hw with hw | hw
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (f := fun i => (c.sl i, 8 * c.n))
      (show EM ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] by decide)),
      Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · have sub : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
        i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by decide
    exact ⟨w, List.mem_append_left _ (List.map_subset _ sub hw), Nat.le_refl _, Nat.le_refl _⟩
  · rw [List.mem_singleton.mp hw]
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), by dsimp only; omega_using [], by dsimp only; omega_using [hz]⟩


/-- `R = [k]G`, by the comb or the ladder, from the table of `k`'s bits, with
`R = O` (for the ladder) and the comb's tables (`hTb`) where the comb reads
them. -/
theorem gMul_ok' (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s (s.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) (publicLookup : Bool := false) :
    WP isa (c.gMul publicLookup).inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_using [hp3])
  unfold Cfg.gMul
  cases hcd : c.comb with
  | none =>
    have hlt : ∀ x ∈ ladR c.ladderCfg, wordsVal s.mem base x c.MP'.n < c.C.p := by
      intro x hx
      have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show sv c _ s i < c.C.p
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F.ap (hmont _)
      · exact lt_of_eq_of_lt F.b3p (hmont _)
      · exact lt_of_eq_of_lt F.gx (hmont _)
      · exact lt_of_eq_of_lt F.gy (hmont _)
      · exact lt_of_eq_of_lt F.onep (Nat.mod_lt _ (by omega_using [hp3]))
      · exact lt_of_eq_of_lt hrx (by omega_using [hp3])
      · exact lt_of_eq_of_lt hry (hmont _)
      · exact lt_of_eq_of_lt hrz (by omega_using [hp3])
    have hG : Rep c.C (tmv c.C c.n base s (c.sl GX)) (tmv c.C c.n base s (c.sl GY))
        (tmv c.C c.n base s (c.sl ONEP)) (G c.C) := by
      show Rep c.C (toM _ _ (wordsVal s.mem _ (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem _ (c.sl GY) c.n))
        (toM _ _ (wordsVal s.mem _ (c.sl ONEP) c.n)) (G c.C)
      rw [F.gx, F.gy, F.onep, toM_cmont hc, toM_cmont hc, toM_one hpR]
      exact rep_affine' hC _ _
    have hR : Rep c.C (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
        (tmv c.C c.n base s (c.sl RZ)) (mul (k >>> (64 * c.n)) (G c.C)) := by
      show Rep c.C (toM _ _ (sv c _ s RX)) (toM _ _ (sv c _ s RY)) (toM _ _ (sv c _ s RZ)) _
      rw [hrx, hry, hrz, toM_cmont hc, toM_zero, shiftRight_eq_zero hkl, mul_zero_pt]
      exact rep_infinity' hC
    have hstep := step_rep (L := c.ladderCfg) (k := k) hC hc.onG (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
        rw [F.ap]; exact toM_cmont hc _)
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
        rw [F.b3p]; exact toM_cmont hc _) hG
    refine WP.mono (ladder_ok (ladLay hc) hpR hs (modP_of hc F.mp) hlt hstep hR ht₀)
      fun s' ⟨K', U', M', L', R'⟩ => ⟨K', ?_, M', L', by rw [Nat.shiftRight_zero] at R'; exact R'⟩
    rw [ladW_eq] at U'
    have hsub : slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
        TMP] ⊆ slW c [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] :=
      List.map_subset _ (by decide)
    exact Unch.cover U' fun w hw => ⟨w, List.mem_append_left _ (hsub hw), Nat.le_refl _, Nat.le_refl _⟩
  | some d =>
    obtain ⟨hTM, hout⟩ := hTb d hcd
    exact gMulComb_ok' hc hcd hs F.mp F.zero hkl ht₀ hTM hout fun s₁ hs₁ hM₁ hF =>
      tcomb_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1) hc.p_lt hs₁
        hM₁ hF publicLookup

/-- `R = [k]G` for a secret `k` (`gMulK`): by the comb with Booth's digits for
a curve whose comb has them, else as `gMul`. -/
theorem gMulK_ok' (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {base : Addr} {g : Reg → BitVec 64}
    {s : State} (hs : Scr s base size) (F : Fixed c base g s.mem) {k : Nat} (hkl : k < 2 ^ (64 * c.n))
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (hTb : ∀ d, c.comb = some d → TblMem s (s.syms d.tsym) (c.combWords d) ∧
      ∀ i < (c.combWords d).length, ∀ b < 8,
        size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.gMulK.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul k (G c.C)) := by
  unfold Cfg.gMulK
  cases hcd : c.comb with
  | none => exact gMul_ok' hc hC hT hs F hkl hrx hry hrz ht₀ hTb
  | some d =>
    cases hj : d.jac
    · simp only [hj, Bool.false_eq_true, ↓reduceIte]
      exact gMul_ok' hc hC hT hs F hkl hrx hry hrz ht₀ hTb
    · simp only [hj, ↓reduceIte]
      obtain ⟨hTM, hout⟩ := hTb d hcd
      exact gMulComb_ok' hc hcd hs F.mp F.zero hkl ht₀ hTM hout fun s₁ hs₁ hM₁ hF =>
        tcombJ_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1) hc.p_lt
          (by show 1 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega_using []) ((hT d hcd).2 hj) hkl hs₁ hM₁ hF

/-- `R = [k]G` for a secret `k`, after the setup and the tables. -/
theorem gMulK_ok (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat} {s₀ : State} (hp : Pre c s₀)
    {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s) :
    WP isa c.gMulK.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) :=
  gMulK_ok' hc hC hT hS.scr hS.fixed (hS.k ▸ wordsVal_lt _ _ _ _) hS.rx hS.ry hS.rz (hS.t₀ rfl) fun d hcd => by
    rw [hS.syms]; exact tbl_of hcd hp hS.rd hS.unch

end VG.Proof.Ecdsa.X86_64

end

end

/-!
# `vg_<curve>_mul_base`'s body on x86-64

`Cfg.mulBaseBody`: the table of `k`'s bits (`bits_ok`), from the scalar in
`K`'s slot, then `[k]G` into `R` by the comb (`gMulComb_ok'`, `tcomb_ok`),
which reads `p` and zero and writes only its slots, `b R mod p` in `EM` and
the word past the table (`mulBaseBody_ok`): what `gMulK_ok` gives, from
`p`, zero and the curve's tables alone. `Cfg.mulBaseFn` runs it between
saving the callee-saved registers in its slots (`mulBaseSlots`: `ACC`'s, and
`TT`'s for fewer than six words) and restoring them (`mulBaseFn_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `R = [k]G` for the `k` in `K`'s slot, with the table of its bits, from
`p`, zero and the comb's tables: by complete additions, or by Booth's digits
and Jacobian additions for a comb that has them (`jac`). -/
theorem mulBaseBody_ok (hc : BaseCfgOk c) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : wordsVal s.mem base (c.sl MP) c.n = c.C.p) (hz : wordsVal s.mem base (c.sl ZERO) c.n = 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.mulBaseBody.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (gW c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (wordsVal s.mem base (c.sl K) c.n) (G c.C)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  show WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) c.gMulK.inline) s _
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono_syms (bits_ok hs h0 (by omega_using [h7]) (sl_le c h7 (i := K) (by decide)) hsz
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0 (.inl (by decide)); omega_using [this])))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n + 8)] s.mem s₁.mem := fun x hx =>
    O₁ x (by have := hx _ (List.mem_singleton_self _); dsimp only at this; omega_using [this])
  have hap : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n + 8)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_pad hi
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch U₁ h7 hn (i := MP) (by decide) (hap (by decide))).trans hmp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch U₁ h7 hn (i := ZERO) (by decide) (hap (by decide))).trans hz
  have hTM₁ : TblMem s₁ (s.syms d.tsym) (c.combWords d) :=
    hTM.of_unch (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; have := bitsAt_le c h7 (j := 1) (by decide)
      rw [bitsAt_eq] at this ⊢; dsimp only; omega_using [this]) hout
  have hG : WP isa c.gMulK.inline s₁ fun s' => KeepRegs (powClob c.n) s₁ s' ∧ Unch base (gW c) s₁.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (wordsVal s.mem base (c.sl K) c.n) (G c.C)) := by
    unfold Cfg.gMulK
    rw [hcd]
    dsimp only
    split
    · rename_i hj
      exact gMulComb_ok' hc hcd hs₁ hmp₁ hz₁ (wordsVal_lt _ _ _ _) b₁ (by rw [sy₁]; exact hTM₁)
        (by rw [sy₁]; exact hout) fun s₂ hs₂ hM₂ hF =>
          tcombJ_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1)
            hc.p_lt (by show 1 ≤ bitsAt c.n 0; rw [bitsAt_eq]; omega_using []) ((hT d hcd).2 hj)
            (wordsVal_lt _ _ _ _) hs₂ hM₂ hF
    · unfold Cfg.gMul
      rw [hcd]
      exact gMulComb_ok' hc hcd hs₁ hmp₁ hz₁ (wordsVal_lt _ _ _ _) b₁ (by rw [sy₁]; exact hTM₁)
        (by rw [sy₁]; exact hout) fun s₂ hs₂ hM₂ hF =>
          tcomb_ok (tcombLay hc (hc.comb d hcd)) hC (hc.comb_am3 d hcd) hc.onG (tcombVals hc hC (hT d hcd).1)
            hc.p_lt hs₂ hM₂ hF false
  refine WP.mono hG fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, ?_, M', L', R'⟩
  · refine (k₁.mono fun r hr => ?_).trans K'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  · refine Unch.cover (U₁.trans U') fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨w, List.mem_append_right _ hw, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨w, hw, Nat.le_refl _, Nat.le_refl _⟩

theorem mulBaseSlots_sub {i : Nat} (h : i ∈ c.mulBaseSlots) : i = ACC ∨ i = TT := by
  unfold Cfg.mulBaseSlots at h
  split at h <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at h <;> omega_using [h]

/-- What `gMulKC` may write: `gMulK`'s, and the slots where
`vg_<curve>_mul_base` keeps the callee-saved registers. -/
abbrev gWA (c : Cfg) : List (Nat × Nat) := gW c ++ slW c c.mulBaseSlots

theorem not_mulBaseSlots {i : Nat} (h : i ∉ [ACC, TT]) : i ∉ c.mulBaseSlots := fun h' => h (by
  rcases mulBaseSlots_sub h' with rfl | rfl <;> simp)

/-- Each register `vg_<curve>_mul_base` keeps is in one of its slots: `ACC`'s,
or for fewer than six words (of at least three, so that `ACC`'s and `TT`'s
slots hold the six registers) `TT`'s. -/
theorem mulBaseSaved_slots (h3 : 3 ≤ c.n) :
    ∀ p ∈ c.mulBaseSaved, ∃ i ∈ c.mulBaseSlots, c.sl i ≤ p.2 ∧ p.2 + 8 ≤ c.sl i + 8 * c.n := by
  have hA : ACC ∈ c.mulBaseSlots := by unfold Cfg.mulBaseSlots; split <;> simp
  have hT : c.n < 6 → TT ∈ c.mulBaseSlots := fun h => by unfold Cfg.mulBaseSlots; simp [h]
  have key : ∀ d, d ≤ 40 → d % 8 = 0 → ∃ i ∈ c.mulBaseSlots,
      c.sl i ≤ (if d < 8 * c.n then c.sl ACC + d else c.sl TT + (d - 8 * c.n)) ∧
      (if d < 8 * c.n then c.sl ACC + d else c.sl TT + (d - 8 * c.n)) + 8 ≤ c.sl i + 8 * c.n := by
    intro d hd h8
    by_cases h : d < 8 * c.n
    · simp only [h, ↓reduceIte]
      exact ⟨ACC, hA, by omega_using [], by omega_using [h8, h]⟩
    · simp only [h, ↓reduceIte]
      exact ⟨TT, hT (by omega_using [hd, h]), by omega_using [], by omega_using [h3, hd]⟩
  intro p hp
  simp only [Cfg.mulBaseSaved, Cfg.saved, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> exact key _ (by decide) (by decide)

theorem mulBaseSaved_spill (hc : BaseCfgOk c) (h3 : 3 ≤ c.n) : Spill.Slots c.mulBaseSaved := by
  -- The slots depend only on `c.n`: decided once for each of its few values.
  have key : ∀ n < 10, 3 ≤ n → Spill.Slots (Cfg.saved.map fun p : Reg × Nat =>
      (p.1, if p.2 < 8 * n then 64 + 8 * n * ACC + p.2 else 64 + 8 * n * TT + (p.2 - 8 * n))) := by
    decide
  rw [Cfg.mulBaseSaved, sl_eq c ACC, sl_eq c TT]
  exact key c.n hc.n10 h3

/-- `vg_<curve>_mul_base`, for a curve of at least three words: the
callee-saved registers kept (saved in its slots, `mulBaseSlots`, and
restored), and what its body gives (`mulBaseBody_ok`), having written also
those slots. -/
theorem mulBaseFn_ok (hc : BaseCfgOk c) (h3 : 3 ≤ c.n) (hC : Law c.C) (hT : CombTbls c) {d : CombData}
    (hcd : c.comb = some d) {base : Addr} {s : State} (hs : Scr s base size)
    (hmp : wordsVal s.mem base (c.sl MP) c.n = c.C.p) (hz : wordsVal s.mem base (c.sl ZERO) c.n = 0)
    (hTM : TblMem s (s.syms d.tsym) (c.combWords d))
    (hout : ∀ i < (c.combWords d).length, ∀ b < 8,
      size ≤ ofs base (s.syms d.tsym + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 b)) :
    WP isa c.mulBaseFn.inline s fun s' => (∀ r, r ∉ powClob c.n → s'.gpr r = s.gpr r) ∧
      (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      s'.syms = s.syms ∧ Unch base (gWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (wordsVal s.mem base (c.sl K) c.n) (G c.C)) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hsl := mulBaseSaved_slots (c := c) h3
  have hle : ∀ i ∈ c.mulBaseSlots, c.sl i + 8 * c.n ≤ size := fun i hi =>
    sl_le c h7 (by rcases mulBaseSlots_sub hi with rfl | rfl <;> decide)
  show WP isa (.seq (.block (Spill.saveCode .rdi c.mulBaseSaved)) (.seq c.mulBaseBody.inline
    (.block (Spill.restoreCode .rdi c.mulBaseSaved)))) s _
  -- Save.
  refine WP.seq (WP.mono_syms (Spill.save_ok .rdi c.mulBaseSaved s fun p hp => ?_)
    fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ sy₁ => ?_)
  · rw [hs.rdi]
    obtain ⟨i, hi, -, h₂⟩ := hsl p hp
    have := hle i hi
    exact ⟨_, hs.wr, Offset.contains_base base (by omega_using [h₂, this]) (by omega_using [hn, h₂, this])⟩
  rw [hs.rdi] at m₁
  have U₁ : Unch base (slW c c.mulBaseSlots) s.mem s₁.mem := m₁ ▸ saveMem_unch_of _ _ _ _ _ fun p hp => by
    obtain ⟨i, hi, h₁, h₂⟩ := hsl p hp
    have := hle i hi
    exact ⟨_, List.mem_map_of_mem hi, h₁, h₂, by dsimp only; omega_using [hsz, this]⟩
  have sv₁ : Spill.Saved s₁.mem base s.gpr c.mulBaseSaved :=
    m₁ ▸ Spill.saveMem_saved _ _ _ _ (mulBaseSaved_spill hc h3)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hn⟩
  have hmp₁ : wordsVal s₁.mem base (c.sl MP) c.n = c.C.p :=
    (sv_unch U₁ h7 hn (i := MP) (by decide) (apart_slW (not_mulBaseSlots (by decide)))).trans hmp
  have hz₁ : wordsVal s₁.mem base (c.sl ZERO) c.n = 0 :=
    (sv_unch U₁ h7 hn (i := ZERO) (by decide) (apart_slW (not_mulBaseSlots (by decide)))).trans hz
  have hk₁ : wordsVal s₁.mem base (c.sl K) c.n = wordsVal s.mem base (c.sl K) c.n :=
    sv_unch U₁ h7 hn (i := K) (by decide) (apart_slW (not_mulBaseSlots (by decide)))
  have hTM₁ : TblMem s₁ (s₁.syms d.tsym) (c.combWords d) := by
    rw [sy₁]
    exact hTM.of_unch (by rw [rd₁, wr₁]) U₁ (fun w hw => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have := hle i hi; dsimp only; omega_using [this]) hout
  -- The body.
  refine WP.seq (WP.mono_syms (mulBaseBody_ok hc hC hT hcd hs₁ hmp₁ hz₁ hTM₁
    (by rw [sy₁]; exact hout)) fun s₂ ⟨K₂, U₂, M₂, L₂, R₂⟩ sy₂ => ?_)
  rw [hk₁] at R₂
  have sv₂ : Spill.Saved s₂.mem base s.gpr c.mulBaseSaved := fun p hp => by
    obtain ⟨i, hi, h₁, h₂⟩ := hsl p hp
    have := hle i hi
    refine (U₂.word (d := p.2) (fun w hw => ?_) (by omega_using [hn, h₂, this])).trans (sv₁ p hp)
    have ap : c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
      rcases mulBaseSlots_sub hi with rfl | rfl
      · exact apart_gW (c := c) (i := ACC) (by decide) (by decide) w hw
      · exact apart_gW (c := c) (i := TT) (by decide) (by decide) w hw
    rcases ap with h | h <;> [left; right] <;> omega_arith
  have rdi₂ : s₂.gpr .rdi = base := by rw [K₂.gpr _ (rdi_not_powClob _), g₁, hs.rdi]
  -- Restore.
  refine WP.mono_syms (Spill.restore_ok .rdi c.mulBaseSaved s.gpr s₂ (by
      simp [Cfg.mulBaseSaved, Cfg.saved]) (fun p hp => ?_) (by rw [rdi₂]; exact sv₂))
    fun s' ⟨gs, go, ms, rds, wrs⟩ sy' => ?_
  · rw [rdi₂, K₂.wr, wr₁]
    obtain ⟨i, hi, -, h₂⟩ := hsl p hp
    have := hle i hi
    exact ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base (by omega_using [h₂, this]) (by omega_using [hn, h₂, this])⟩
  have hsv : c.mulBaseSaved.map Prod.fst = Cfg.saved.map Prod.fst := by
    simp [Cfg.mulBaseSaved, Cfg.saved]
  rw [hsv] at gs go
  refine ⟨fun r hr => ?_, gs, by rw [rds, K₂.rd, rd₁], by rw [wrs, K₂.wr, wr₁], ?_, ?_,
    by rw [ms]; exact M₂, by rw [ms]; exact L₂, ?_⟩
  · by_cases h : r ∈ Cfg.saved.map Prod.fst
    · exact gs r h
    · rw [go r h, K₂.gpr r hr, g₁]
  · rw [sy', sy₂, sy₁]
  · refine Unch.mono (ms ▸ U₁.trans U₂ : Unch base (slW c c.mulBaseSlots ++ gW c) s.mem s'.mem) fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_right _ hw
    · exact List.mem_append_left _ hw
  · have e : ∀ x, tmv c.C c.n base s' x = tmv c.C c.n base s₂ x := fun x => by
      show toM _ _ _ = toM _ _ _; rw [ms]
    rw [e, e, e]; exact R₂

/-! ## `R = [k]G` in the signature and the public key: `gMulKC` -/

/-- What `mulRun` needs of a curve: four, five, six or eight words, and, as
it runs, `vg_<curve>_mul` calling nothing, or `mulAdd`'s additions' products
written out. -/
def MulFnOk (c : Cfg) : Prop :=
  (c.n = 4 ∨ c.n = 6 ∨ c.n = 8 ∨ c.n = 5) ∧ (c.mulAdd = false → c.mulFn.noCalls = true) ∧
    (c.mulAdd = true → Mont.callOf c.MP' = none)

/-- What a call of `vg_<curve>_mul_base` or `vg_<curve>_mul` needs of the
curve: for the first, a comb and at least three words (so that its slots
hold the six callee-saved registers); for the second, four words (which it
keeps the six registers in `xmm` registers for, as the inversions); and
products written out (the functions call no other, but `mulAdd`'s ladder,
inline, its additions, whose products are written out: `MulFnOk`). -/
def MulBaseOk (c : Cfg) : Prop :=
  (c.mulBase.isSome = true → ∃ d, c.comb = some d ∧ 3 ≤ c.n ∧ c.mulBaseFn.noCalls = true) ∧
    (c.mul.isSome = true → MulFnOk c)

/-- `MulBaseOk`, but `vg_<curve>_mul_base` may call functions (P-521's, its
products), which the proofs run inlined (`gMulKCI`). -/
def MulBaseOkI (c : Cfg) : Prop :=
  (c.mulBase.isSome = true → ∃ d, c.comb = some d ∧ 3 ≤ c.n) ∧ (c.mul.isSome = true → MulFnOk c)

theorem MulBaseOk.toI {c : Cfg} (h : MulBaseOk c) : MulBaseOkI c :=
  ⟨fun hm => let ⟨d, h₁, h₂, _⟩ := h.1 hm; ⟨d, h₁, h₂⟩, h.2⟩

/-- `R = [k]G` as the proofs run it: `gMulKC` inlined, but a call of
`vg_<curve>_mul_base` its code with its own calls inlined. -/
def gMulKCI (c : Cfg) : Prog isa :=
  match c.mulBase with
  | some _ => c.mulBaseFn.inline
  | none => c.gMulKC.inline

/-- Where `vg_<curve>_mul_base` calls nothing, `gMulKCI` is `gMulKC` inlined. -/
theorem gMulKC_inline {c : Cfg} (h : MulBaseOk c) : c.gMulKC.inline = gMulKCI c := by
  unfold gMulKCI
  cases hm : c.mulBase with
  | some C =>
    obtain ⟨_, _, _, hnc⟩ := h.1 (by rw [hm]; rfl)
    show (Cfg.gMulKC c).inline = _
    unfold Cfg.gMulKC
    simp only [hm]
    show c.mulBaseFn = _
    rw [Code.inline_of_noCalls hnc]
  | none => rfl

theorem apart_gWA {i : Nat} (hi : i < 45)
    (hl : i ∉ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM]) (ha : i ∉ [ACC, TT]) :
    ∀ w ∈ gWA c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_gW hi hl) (apart_slW (not_mulBaseSlots ha))

theorem fixedOk_gWA : FixedOk c (gWA c) :=
  FixedOk.append fixedOk_gW (fixedOk_slW
    (fun i hi => .inr (by rcases mulBaseSlots_sub hi with rfl | rfl <;> decide))
    (fun h => by rcases mulBaseSlots_sub h with h | h <;> simp [ACC, TT] at h)
    (fun h => by rcases mulBaseSlots_sub h with h | h <;> simp [ACC, TT] at h))

theorem tbl_apart_gWA {j t : Nat} (hj : j = 1 ∨ j = 2) (ht : t < 64 * c.n)
    (hj1 : j ≠ 1 ∨ c.n ≠ 9 := by sl_or) :
    ∀ w ∈ gWA c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_gW hj ht hj1)
    (tbl_apart_slW (fun i hi => by rcases mulBaseSlots_sub hi with rfl | rfl <;> decide) j t ht
      (.inl fun h => by rcases mulBaseSlots_sub h with h | h <;> simp [ACC, TT, TMP] at h))

theorem flag_unch_gWA {base : Addr} {m m' : Mem} (hu : Unch base (gWA c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega_using [h0, hn, hF])
  rcases apart_gWA (c := c) (i := FLAG) (by decide) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega_using [h0, h])
  · exact Or.inr h

end VG.Proof.Ecdsa.X86_64

end

end

/-!
# `vg_<curve>_mul` on x86-64, and `R = [k]G` by its call

`Cfg.mulBody`: the table of `k`'s bits (`bits_ok`), from the scalar in `K`'s
slot, `Q` (in `R`'s first two slots) copied to `ACC` and `PT`, `R` the point
at infinity (copies of zero and one, `copy_ok`), then `R = [k]Q` by the
ladder (`ladder_ok`, `step_rep'`, with the formulas for `a = 0` if the curve's `a`
is zero), which reads `p`, `a R` and `3 b R` from
their slots and writes only its slots, `R`'s, `ACC`'s, `PT`'s and the table
of bits (`mulBody_ok`). `Cfg.mulFn` runs it between copying the callee-saved
registers to `xmm0`–`xmm5` and back (`mulFn_ok`), as the inversions do.
`gMulKC_ok`: `R = [k]G` in
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
      obtain hl : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX,
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
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  obtain sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
  obtain ap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    rcases sl_apart c h with h | h <;> omega_arith
  show WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl PT) (c.sl RY) ++
      copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO)))
      (ladder c.mulLadder (c.C.a == 0)).inline)) s _
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (by omega_arith) (sz (i := K) (by decide)) hsz
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0 (.inl (by decide)); omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁ : Unch base [(bitsAt c.n 0, 64 * c.n + 8)] s.mem s₁.mem := fun x hx =>
    O₁ x (by have := hx _ (List.mem_singleton_self _); dsimp only at this; omega_arith)
  -- `Q` to `ACC` and `PT`, and `R` the point at infinity.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl ACC) (a := c.sl RX)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₂ (o := c.sl PT) (a := c.sl RY)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₃ (o := c.sl RX) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₄ ⟨v₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₄ (o := c.sl RY) (a := c.sl ONEP)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₅ ⟨v₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₅ (o := c.sl RZ) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  -- What each copy leaves.
  obtain U₂ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC]) s.mem s₂.mem := U₁.trans O₂.unch
  obtain U₃ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT]) s.mem s₃.mem := U₂.trans O₃.unch
  obtain U₄ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX]) s.mem s₄.mem :=
    U₃.trans O₄.unch
  obtain U₅ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY]) s.mem s₅.mem :=
    U₄.trans O₅.unch
  obtain U₆ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY, RZ]) s.mem s₆.mem :=
    U₅.trans O₆.unch
  obtain U₂₆ : Unch base (slW c [PT, RX, RY, RZ]) s₂.mem s₆.mem :=
    ((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch
  obtain U₃₆ : Unch base (slW c [RX, RY, RZ]) s₃.mem s₆.mem := (O₄.unch.trans O₅.unch).trans O₆.unch
  obtain U₄₆ : Unch base (slW c [RY, RZ]) s₄.mem s₆.mem := O₅.unch.trans O₆.unch
  have U₅₆ : Unch base (slW c [RZ]) s₅.mem s₆.mem := O₆.unch
  obtain e₁ := fun {i} (hi : i < 45) => sv_unch U₁ h7 hn hi (apart_pad hi)
  obtain acc₆ : sv c base s₆ ACC = sv c base s RX :=
    (sv_unch U₂₆ h7 hn (i := ACC) (by decide) (apart_slW (by decide))).trans (v₂.trans (e₁ (by decide)))
  obtain pt₆ : sv c base s₆ PT = sv c base s RY :=
    (sv_unch U₃₆ h7 hn (i := PT) (by decide) (apart_slW (by decide))).trans
      (v₃.trans (sv_unch U₂ h7 hn (i := RY) (by decide) (apart_bits_slW (by decide) (by decide))))
  obtain rx₆ : sv c base s₆ RX = 0 :=
    (sv_unch U₄₆ h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans
      (v₄.trans ((sv_unch U₃ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz))
  obtain one₄ : sv c base s₄ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (sv_unch U₄ h7 hn (i := ONEP) (by decide) (apart_bits_slW (by decide) (by decide))).trans hone
  obtain ry₆ : sv c base s₆ RY = c.mont 1 := by
    obtain h := (sv_unch U₅₆ h7 hn (i := RY) (by decide) (apart_slW (by decide))).trans (v₅.trans one₄)
    rw [show c.mont 1 = 2 ^ (64 * c.n) % c.C.p by show 1 * c.R % c.C.p = _; rw [Nat.one_mul]; rfl]
    exact h
  obtain rz₆ : sv c base s₆ RZ = 0 :=
    v₆.trans ((sv_unch U₅ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz)
  obtain e₆ := fun {i} (hi : i < 45) (hl : i ∉ [ACC, PT, RX, RY, RZ]) =>
    sv_unch U₆ h7 hn hi (apart_bits_slW hi hl)
  obtain mp₆ : sv c base s₆ MP = c.C.p := (e₆ (i := MP) (by decide) (by decide)).trans hmp
  obtain ap₆ : sv c base s₆ AP = c.mont c.C.a := (e₆ (i := AP) (by decide) (by decide)).trans hap
  obtain b3₆ : sv c base s₆ B3P = c.mont (3 * c.C.b) := (e₆ (i := B3P) (by decide) (by decide)).trans hb3
  obtain one₆ : sv c base s₆ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (e₆ (i := ONEP) (by decide) (by decide)).trans hone
  obtain U₂₆' : Unch base (slW c [ACC, PT, RX, RY, RZ]) s₁.mem s₆.mem :=
    ((((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch)
  obtain k₆' : ∀ t < 64 * c.n, s₆.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch U₂₆' h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t ht)]
    exact b₁ t ht
  -- The ladder.
  obtain hlt : ∀ x ∈ ladR c.mulLadder, wordsVal s₆.mem base x c.MP'.n < c.C.p := by
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
  obtain hG : Rep c.C (tmv c.C c.n base s₆ (c.sl ACC)) (tmv c.C c.n base s₆ (c.sl PT))
      (tmv c.C c.n base s₆ (c.sl ONEP)) (ptQ c base s) := by
    show Rep c.C (toM _ _ (sv c base s₆ ACC)) (toM _ _ (sv c base s₆ PT)) (toM _ _ (sv c base s₆ ONEP))
      (Point.affine (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)))
    rw [acc₆, pt₆, one₆, toM_one hpR]
    exact rep_affine' hC _ _
  obtain hstep := step_rep' (L := c.mulLadder) (k := sv c base s K) (a0 := c.C.a == 0) hC hQ
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ AP) = _; rw [ap₆]; exact toM_cmont hc _)
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₆ B3P) = _; rw [b3₆]; exact toM_cmont hc _) hG
    fun h0 => ⟨by rw [beq_iff_eq.mp h0]; rfl, by
      show toM _ _ (sv c base s₆ ONEP) = 1; rw [one₆]; exact toM_one hpR⟩
  obtain hR : Rep c.C (tmv c.C c.n base s₆ (c.sl RX)) (tmv c.C c.n base s₆ (c.sl RY))
      (tmv c.C c.n base s₆ (c.sl RZ)) (mul (sv c base s K >>> (64 * c.n)) (ptQ c base s)) := by
    show Rep c.C (toM _ _ (sv c base s₆ RX)) (toM _ _ (sv c base s₆ RY)) (toM _ _ (sv c base s₆ RZ)) _
    rw [rx₆, ry₆, rz₆, toM_cmont hc, toM_zero, shiftRight_eq_zero (wordsVal_lt _ _ _ _), mul_zero_pt]
    exact rep_infinity' hC
  obtain hk1 : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  obtain hk2 : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => hk1 r (by
    simp only [List.mem_singleton] at hr; simp [hr])
  refine WP.mono (ladder_ok (ladLayM hc) hpR hs₆ (modP_of hc mp₆) hlt hstep hR k₆')
    fun s' ⟨K', U', M', L', R'⟩ => ⟨?_, ?_, M', L', ?_⟩
  · exact ((((((k₁.mono hk1).trans (k₂.mono hk2)).trans (k₃.mono hk2)).trans (k₄.mono hk2)).trans
      (k₅.mono hk2)).trans (k₆.mono hk2)).trans K'
  · rw [ladWM_eq] at U'
    obtain hsub : ∀ w ∈ ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, PT, RX, RY, RZ]) ++
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

/-- `vg_<curve>_mul`, for a curve of four, five, six or eight words: what its body gives
(`mulBody_ok`); the registers it copies to `xmm` registers and back are
among those its body changes (`powClob`). -/
theorem mulFn_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8 ∨ c.n = 5) (hC : Law c.C) {base : Addr} {s : State}
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
  obtain hkept : ∀ r ∈ Cfg.invKeptX.map Prod.fst, r ∈ powClob c.n := by
    rcases h4 with h | h | h | h <;> rw [h] <;> decide
  show WP isa (.seq (.block _) (.seq c.mulBody.inline (.block _))) s _
  refine WP.seq (WP.mono (savesX_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  obtain ev : ∀ i, sv c base s₁ i = sv c base s i := fun i => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  obtain eQ : ptQ c base s₁ = ptQ c base s := by
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

/-! ## The ladder of `mulAdd`, whose additions are calls

`Cfg.ladderBodyA` runs the iteration of `ladderBody` with the additions as
calls of `vg_<curve>_add_complete` (`Cfg.addComplete`, `D = R + T`): `T = R`
and `D = R + T`, then `R = D`, `T = G` and `D = R + T`, and `R = D` if the
bit is set. Its proof is `ladderBody_ok`'s, its steps on the field values in
the slots (`Inv`): the copies' by `copyPointFields_ok`, the additions' by
`rcb_ok`, and the selection's (`selPtSelf_ok`). -/

/-- Field operations call nothing where the products are not calls
(`Mont.callOf M = none`): so a call of them, such as the complete addition's
function (`vg_<curve>_add_complete`), runs as they do inlined. -/
theorem fprogB_noCalls {M : Mod} (h : Mont.callOf M = none) (ops : List FOp) :
    (fprogB M ops).noCalls = true := by
  obtain hop : ∀ op, (opProg M op).noCalls = true := fun op => by
    cases op <;> simp [opProg, opCall?, h, Code.noCalls]
  unfold fprogB
  induction ops with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => exact hop a
    | cons b l => simp only [List.map_cons, progs, Code.noCalls, Bool.and_eq_true] at ih ⊢; exact ⟨hop a, ih⟩

/-- `[o] = [b]` by the mask `rcx` if it is all ones, else unchanged. -/
theorem selPtSelf_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) (c : Bool)
    (hc : s.gpr .rcx = (if c then BitVec.allOnes 64 else 0)) {n : Nat} {o b : Pt}
    (hin : ∀ d ∈ [o.x, o.y, o.z, b.x, b.y, b.z], d + 8 * n ≤ size)
    (hoo : (o.x + 8 * n ≤ o.y ∨ o.y + 8 * n ≤ o.x) ∧ (o.x + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.x) ∧
      (o.y + 8 * n ≤ o.z ∨ o.z + 8 * n ≤ o.y))
    (hab : ∀ d ∈ [o.x, o.y, o.z], ∀ e ∈ [b.x, b.y, b.z], d + 8 * n ≤ e ∨ e + 8 * n ≤ d) :
    WP isa (.block (selPt n o o b)) s fun s' =>
      wordsVal s'.mem base o.x n = (if c then wordsVal s.mem base b.x n else wordsVal s.mem base o.x n) ∧
      wordsVal s'.mem base o.y n = (if c then wordsVal s.mem base b.y n else wordsVal s.mem base o.y n) ∧
      wordsVal s'.mem base o.z n = (if c then wordsVal s.mem base b.z n else wordsVal s.mem base o.z n) ∧
      KeepRegs [.rax, .rdx] s s' ∧
      ∀ x, (ofs base x < o.x ∨ o.x + 8 * n ≤ ofs base x) → (ofs base x < o.y ∨ o.y + 8 * n ≤ ofs base x) →
        (ofs base x < o.z ∨ o.z + 8 * n ≤ ofs base x) → s'.mem x = s.mem x := by
  have hn := hs.nowrap
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hin hab
  obtain ⟨iox, ioy, ioz, ibx, iby, ibz⟩ := hin
  obtain ⟨⟨xbx, xby, xbz⟩, ⟨ybx, yby, ybz⟩, ⟨zbx, zby, zbz⟩⟩ := hab
  obtain ⟨xy, xz, yz⟩ := hoo
  rw [selPt, List.append_assoc, WP.block_append_iff]
  refine WP.mono (sel_ok c n hs hc iox iox ibx (Or.inl (Nat.le_refl _)) (by omega_using [xbx]))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (sel_ok c n hs₁ (by rw [k₁.gpr _ (by decide), hc]) ioy ioy iby (Or.inl (Nat.le_refl _))
    (by omega_using [yby])) fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (sel_ok c n hs₂ (by rw [k₂.gpr _ (by decide), k₁.gpr _ (by decide), hc]) ioz ioz ibz
    (Or.inl (Nat.le_refl _)) (by omega_using [zbz])) fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  refine ⟨?_, ?_, ?_, (k₁.trans k₂).trans k₃, fun x h₁ h₂ h₃ => by rw [O₃ x h₃, O₂ x h₂, O₁ x h₁]⟩
  · rw [O₃.wordsVal (d := o.x) (by omega_using [xz]) (by omega_using [iox, hn]),
      O₂.wordsVal (d := o.x) (by omega_using [xy]) (by omega_using [iox, hn]), e₁]
  · rw [O₃.wordsVal (d := o.y) (by omega_using [yz]) (by omega_using [ioy, hn]), e₂,
      O₁.wordsVal (d := o.y) (by omega_using [xy]) (by omega_using [ioy, hn]),
      O₁.wordsVal (d := b.y) (by omega_using [xby]) (by omega_using [iby, hn])]
  · rw [e₃, O₂.wordsVal (d := o.z) (by omega_using [yz]) (by omega_using [ioz, hn]),
      O₂.wordsVal (d := b.z) (by omega_using [ybz]) (by omega_using [ibz, hn]),
      O₁.wordsVal (d := o.z) (by omega_using [xz]) (by omega_using [ioz, hn]),
      O₁.wordsVal (d := b.z) (by omega_using [xbz]) (by omega_using [ibz, hn])]

theorem ladLayMA (hc : BaseCfgOk c) : LadLay c.mulLadderA size := by
  have hn := hc.n0
  have h7 := hc.n10
  refine ⟨?_, rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
      (lr := [AP, PT, RX, RY, RZ, RX, RY, RZ]) rfl rfl (by decide) (by decide),
    rcbApart_of hn (lw := [T0, T1, T2, T3, T4, T5, TX, TY, TZ])
      (lr := [AP, PT, DX, DY, DZ, ACC, EM, ONEP]) rfl rfl (by decide) (by decide), ?_,
    ⟨fun h => by have := sl_inj c hn (i := RX) (j := RY) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RX) (j := RZ) h; exact absurd this (by decide),
      fun h => by have := sl_inj c hn (i := RY) (j := RZ) h; exact absurd this (by decide)⟩, ?_,
    ⟨show 1 ≤ 64 * c.n by omega_arith, show 64 * c.n < 2 ^ 16 by omega_arith⟩, bitsAt_le c h7 (by decide), ?_⟩
  · exact lay_map hc rfl rfl rfl (l := [AP, PT, ACC, EM, ONEP, RX, RY, RZ, T0, T1, T2, T3, T4, T5,
      DX, DY, DZ, TX, TY, TZ]) (by decide)
  · exact map_sl_disj hn (l₁ := [AP, PT, ACC, EM, ONEP])
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
      exact Or.inr (sl_below_bits c (hl i hi) 0 0 (.inl fun h => by subst h; exact absurd hi (by decide)))
    · rcases tmp_apart_bits c (j := 0) (.inl (by decide)) (by decide) (64 * c.n) (by omega_arith) with h | h
      · exact Or.inr (by show c.sl TMP + 8 * c.n ≤ bitsAt c.n 0; exact h)
      · exact Or.inl (by show bitsAt c.n 0 + 64 * c.n ≤ c.sl TMP; exact h)

theorem ladWMA_eq (c : Cfg) : ladW c.mulLadderA = slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ,
    T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP] := rfl

/-- The calls' addition `D = R + T` writes apart from what it reads. -/
theorem rcbApartRT (hc : BaseCfgOk c) :
    RcbApart c.mulLadderA.S c.mulLadderA.R c.mulLadderA.T c.mulLadderA.D :=
  rcbApart_of hc.n0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ])
    (lr := [AP, PT, RX, RY, RZ, TX, TY, TZ]) rfl rfl (by decide) (by decide)

/-- An iteration of the ladder of `mulAdd`, as `ladderBody_ok`. -/
theorem ladderBodyA_ok (hc : BaseCfgOk c) {C : Curve} {base : Addr} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} (hp : UnitMod C.p (2 ^ (64 * c.mulLadderA.M.n)))
    (hnc : Mont.callOf c.MP' = none) {s₀ : State}
    (hlt₀ : ∀ x ∈ ladRo c.mulLadderA, wordsVal s₀.mem base x c.mulLadderA.M.n < C.p)
    (hstep : Step c.mulLadderA C base s₀ k Q false)
    (hbits : ∀ t < c.mulLadderA.nbits, s₀.mem (off base (c.mulLadderA.bits + t)) =
      if k.testBit t then 1 else 0)
    {j : Nat} {s : State} (hj : 1 ≤ j) (hjn : j ≤ c.mulLadderA.nbits)
    (hI : LadInv c.mulLadderA C base size Q s₀ s j) :
    WP isa c.ladderBodyA.inline s fun s' =>
      LadInv c.mulLadderA C base size Q s₀ s' (j - 1) ∧ s'.zf = some (decide (j - 1 = 0)) := by
  have hL : LadLay c.mulLadderA size := ladLayMA hc
  have hn := hI.scr.nowrap
  have hnb := hL.nbits
  have hro : ∀ x ∈ ladRo c.mulLadderA, wordsVal s.mem base x c.mulLadderA.M.n =
      wordsVal s₀.mem base x c.mulLadderA.M.n :=
    fun x hx => hI.unch.wordsVal
      (hL.apart_w (ladR_slots _ x (mem_ladRo_ladR hx)) (hL.ro x hx))
      (by have := hL.lay.le x (ladR_slots _ x (mem_ladRo_ladR hx)); omega_using [hn, this])
  have hE : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => by rw [tmv, hro x hx]
  have hadd : c.addComplete.noCalls = true := fprogB_noCalls hnc _
  have hSl : ∀ x ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
      c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x, c.mulLadderA.T.y, c.mulLadderA.T.z],
      x ∈ ladSlots c.mulLadderA := ladPts_slots _
  have hap : ∀ x ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
      c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x, c.mulLadderA.T.y, c.mulLadderA.T.z],
      ∀ y ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
      c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x, c.mulLadderA.T.y, c.mulLadderA.T.z],
      x ≠ y → x + 8 * c.mulLadderA.M.n ≤ y ∨ y + 8 * c.mulLadderA.M.n ≤ x :=
    fun x hx y hy hxy => hL.lay.apart x y (hSl x hx) (hSl y hy) hxy
  obtain ⟨rxy, rxz, ryz⟩ := hL.rne
  have hrdt := hL.rdt
  rw [Cfg.ladderBodyA]
  simp only [Code.inline]
  rw [← Code.inline_of_noCalls hadd]
  -- `sub rbx, 1` and `T = R`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (decRbx_ok s hj (by omega_using [hjn, hnb]) hI.rbx) fun s₁ ⟨b₁, k₁⟩ => ?_
  have hm₁ : s₁.mem = s.mem := k₁.2.1
  have I₁ : Inv c.mulLadderA.M base size C.p (· ∈ ladSlots c.mulLadderA) (ladR c.mulLadderA)
      (tmv C c.mulLadderA.M.n base s₁) s₁ := by
    refine ⟨hI.scr.of_keeps k₁ (by decide), by rw [hm₁]; exact hI.mod, ladR_slots _, fun x hx => ?_,
      fun x _ => by rw [tmv, hm₁]⟩
    rw [hm₁]
    simp only [ladR, List.mem_append] at hx
    rcases hx with hx | hx
    · rw [hro x hx]; exact hlt₀ x hx
    · exact hI.lt x hx
  -- The slots of the points.
  have j3 : ∀ {p : Pt} {x : Nat}, x ∈ jacCoords p → x = p.x ∨ x = p.y ∨ x = p.z := fun {p x} hx => by
    simp only [jacCoords, List.mem_cons, List.not_mem_nil, or_false] at hx; exact hx
  have slR : ∀ x ∈ jacCoords c.mulLadderA.R, x ∈ ladSlots c.mulLadderA := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> exact hSl _ (by simp)
  have slD : ∀ x ∈ jacCoords c.mulLadderA.D, x ∈ ladSlots c.mulLadderA := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> exact hSl _ (by simp)
  have slT : ∀ x ∈ jacCoords c.mulLadderA.T, x ∈ ladSlots c.mulLadderA := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> exact hSl _ (by simp)
  have slRo : ∀ x ∈ ladRo c.mulLadderA, x ∈ ladSlots c.mulLadderA := fun x hx =>
    ladR_slots _ x (mem_ladRo_ladR hx)
  have slDW : ∀ x ∈ rcbW c.mulLadderA.S c.mulLadderA.D, x ∈ ladSlots c.mulLadderA := fun x hx =>
    ladWs_slots _ x (by simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr hx))
  have wT : ∀ x ∈ jacCoords c.mulLadderA.T, x ∈ ladWs c.mulLadderA := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> simp [ladWs, rcbW]
  have wR : ∀ x ∈ jacCoords c.mulLadderA.R, x ∈ ladWs c.mulLadderA := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> simp [ladWs]
  have wD : ∀ x ∈ rcbW c.mulLadderA.S c.mulLadderA.D, x ∈ ladWs c.mulLadderA := fun x hx => by
    simp only [ladWs, List.mem_append]; exact Or.inl (Or.inr hx)
  have roW : ∀ x ∈ ladRo c.mulLadderA, ∀ {W : List Nat}, (∀ y ∈ W, y ∈ ladWs c.mulLadderA) → x ∉ W :=
    fun x hx W hW h => hL.ro x hx (hW x h)
  have RnT : ∀ x ∈ jacCoords c.mulLadderA.R, x ∉ jacCoords c.mulLadderA.T := fun x hx h =>
    hrdt x (by rcases j3 hx with rfl | rfl | rfl <;> simp) (by rcases j3 h with h | h | h <;> simp [h])
  have RnD : ∀ x ∈ jacCoords c.mulLadderA.R, x ∉ rcbW c.mulLadderA.S c.mulLadderA.D := fun x hx h =>
    hL.a1.apart x (by rcases j3 hx with rfl | rfl | rfl <;> simp [rcbR]) h
  -- A slot apart from what a step writes keeps its value.
  have tk : ∀ {W : List Nat} {x y : State}, ProgKeep c.mulLadderA.M base W x y → Scr x base size →
      (∀ w ∈ W, w ∈ ladSlots c.mulLadderA) → ∀ {z : Nat}, z ∈ ladSlots c.mulLadderA → z ∉ W →
      tmv C c.mulLadderA.M.n base y z = tmv C c.mulLadderA.M.n base x z := fun hk hs hW _ hz hn => by
    unfold tmv; rw [hk.slot hL.lay hs hW hz hn]
  -- `T = R`.
  refine WP.mono (copyPointFields_ok hL.lay (q := c.mulLadderA.R) (o := c.mulLadderA.T)
    (List.Nodup.sublist (List.sublist_append_right [c.mulLadderA.S.t0, c.mulLadderA.S.t1, c.mulLadderA.S.t2,
      c.mulLadderA.S.t3, c.mulLadderA.S.t4, c.mulLadderA.S.t5] (jacCoords c.mulLadderA.T)) hL.a2.nodup)
    (fun x hx y hy e => RnT x hx (e ▸ hy)) slT I₁
    (fun x hx => List.mem_append_right _ hx)) fun s₂ ⟨E₂, kp₂, I₂, e₂⟩ => ?_
  have hs₂ := kp₂.scr I₁.scr
  simp only [Prod.mk.injEq] at e₂
  obtain tT₂ : ∀ x ∈ [(c.mulLadderA.T.x, c.mulLadderA.R.x), (c.mulLadderA.T.y, c.mulLadderA.R.y),
      (c.mulLadderA.T.z, c.mulLadderA.R.z)],
      tmv C c.mulLadderA.M.n base s₂ x.1 = tmv C c.mulLadderA.M.n base s₁ x.2 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (I₂.val _ (by simp [jacCoords])).trans e₂.1
    · exact (I₂.val _ (by simp [jacCoords])).trans e₂.2.1
    · exact (I₂.val _ (by simp [jacCoords])).trans e₂.2.2
  -- `D = R + T`.
  refine WP.seq (WP.mono (rcb_ok hL.lay hp (rcbApartRT hc) (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact slDW x hx
      · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact slRo _ (by simp [ladRo])
        · exact slRo _ (by simp [ladRo])
        · exact slR _ (by simp [jacCoords])
        · exact slR _ (by simp [jacCoords])
        · exact slR _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords]))
    I₂.to_tmv (fun x hx => by
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [jacCoords, ladR, ladRo])) fun s₃ ⟨k₃, I₃, v₃, _⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have I₃' := I₃.to_tmv
  have hRnd : (jacCoords c.mulLadderA.R).Nodup := by
    simp only [jacCoords, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true, not_false_eq_true]
    exact ⟨⟨rxy, rxz⟩, ryz⟩
  have hTnd : (jacCoords c.mulLadderA.T).Nodup :=
    List.Nodup.sublist (List.sublist_append_right [c.mulLadderA.S.t0, c.mulLadderA.S.t1, c.mulLadderA.S.t2,
      c.mulLadderA.S.t3, c.mulLadderA.S.t4, c.mulLadderA.S.t5] (jacCoords c.mulLadderA.T)) hL.a2.nodup
  have DinW : ∀ x ∈ jacCoords c.mulLadderA.D, x ∈ rcbW c.mulLadderA.S c.mulLadderA.D := fun x hx => by
    rcases j3 hx with rfl | rfl | rfl <;> simp [rcbW]
  -- `R = D` and `T = G`.
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono (copyPointFields_ok hL.lay (q := c.mulLadderA.D) (o := c.mulLadderA.R) hRnd
    (fun x hx y hy e => RnD y hy (e ▸ DinW x hx)) slR I₃'
    (fun x hx => List.mem_append_left _ (DinW x hx))) fun s₄ ⟨E₄, kp₄, I₄, e₄⟩ => ?_
  have hs₄ := kp₄.scr hs₃
  simp only [Prod.mk.injEq] at e₄
  refine WP.mono (copyPointFields_ok hL.lay (q := c.mulLadderA.G) (o := c.mulLadderA.T) hTnd
    (fun x hx y hy e => roW x (by rcases j3 hx with rfl | rfl | rfl <;> simp [ladRo]) wT (e ▸ hy)) slT
    I₄.to_tmv (fun x hx => by
      rcases j3 hx with rfl | rfl | rfl <;> simp [jacCoords, ladR, ladRo])) fun s₅ ⟨E₅, kp₅, I₅, e₅⟩ => ?_
  have hs₅ := kp₅.scr hs₄
  simp only [Prod.mk.injEq] at e₅
  -- `D = R + T` again.
  refine WP.seq (WP.mono (rcb_ok hL.lay hp (rcbApartRT hc) (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact slDW x hx
      · simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact slRo _ (by simp [ladRo])
        · exact slRo _ (by simp [ladRo])
        · exact slR _ (by simp [jacCoords])
        · exact slR _ (by simp [jacCoords])
        · exact slR _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords])
        · exact slT _ (by simp [jacCoords]))
    I₅.to_tmv (fun x hx => by
      simp only [rcbR, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [jacCoords, ladR, ladRo])) fun s₆ ⟨k₆, I₆, v₆, _⟩ => ?_)
  have hs₆ := k₆.scr hs₅
  -- What is written is in `ladW`.
  have toW : ∀ {W : List Nat}, (∀ x ∈ W, x ∈ ladWs c.mulLadderA) →
      ∀ w ∈ W.map (·, 8 * c.mulLadderA.M.n) ++ [(c.mulLadderA.M.tmp, 8 * c.mulLadderA.M.n)],
        w ∈ ladW c.mulLadderA := fun {W} hW w hw => by
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp h
      exact List.mem_append_left _ (List.mem_map_of_mem (hW y hy))
    · exact List.mem_append_right _ h
  have U₀₆ : Unch base (ladW c.mulLadderA) s₀.mem s₆.mem := by
    have u₁ : Unch base (ladW c.mulLadderA) s₀.mem s₁.mem := by rw [hm₁]; exact hI.unch
    refine (u₁.trans ((kp₂.unch.trans (k₃.unch.trans (kp₄.unch.trans (kp₅.unch.trans k₆.unch)))))).mono
      fun w hw => ?_
    rcases List.mem_append.mp hw with h | h
    · exact h
    rcases List.mem_append.mp h with h | h
    · exact toW wT w h
    rcases List.mem_append.mp h with h | h
    · exact toW wD w h
    rcases List.mem_append.mp h with h | h
    · exact toW wR w h
    rcases List.mem_append.mp h with h | h
    · exact toW wT w h
    · exact toW wD w h
  have hrbx₆ : s₆.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₆.gpr _ (rbx_not_clob _), kp₅.gpr _ (rbx_not_clob _), kp₄.gpr _ (rbx_not_clob _),
      k₃.gpr _ (rbx_not_clob _), kp₂.gpr _ (rbx_not_clob _), b₁]
  have hbyte : s₆.mem (off base (c.mulLadderA.bits + (j - 1))) = if k.testBit (j - 1) then 1 else 0 := by
    have hbl := hL.bits
    rw [U₀₆.byte (fun w hw => by have := hL.bits_w w hw; omega_using [hj, hjn, this])
      (by omega_using [hj, hjn, hn, hbl]), hbits _ (by omega_using [hj, hjn])]
  -- The selection.
  rw [WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (bitMask_bool_ok hs₆ hrbx₆ (by have := hL.bits; omega_using [hj, hjn, this]) hbyte)
    fun s₇ ⟨c₇, k₇⟩ => ?_
  have hs₇ := hs₆.of_keeps k₇ (by decide)
  have hm₇ : s₇.mem = s₆.mem := k₇.2.1
  have hinS : ∀ d ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
      c.mulLadderA.D.y, c.mulLadderA.D.z], d + 8 * c.mulLadderA.M.n ≤ size := by
    intro d hd
    refine hL.lay.le d (hSl d ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
    rcases hd with h | h | h | h | h | h <;> simp [h]
  have habS : ∀ d ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z],
      ∀ e ∈ [c.mulLadderA.D.x, c.mulLadderA.D.y, c.mulLadderA.D.z],
      d + 8 * c.mulLadderA.M.n ≤ e ∨ e + 8 * c.mulLadderA.M.n ≤ d := by
    intro d hd e he
    have hd' : d ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
        c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x, c.mulLadderA.T.y, c.mulLadderA.T.z] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd ⊢
      rcases hd with h | h | h <;> simp [h]
    have he' : e ∈ [c.mulLadderA.R.x, c.mulLadderA.R.y, c.mulLadderA.R.z, c.mulLadderA.D.x,
        c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x, c.mulLadderA.T.y, c.mulLadderA.T.z] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      rcases he with h | h | h <;> simp [h]
    have he'' : e ∈ [c.mulLadderA.D.x, c.mulLadderA.D.y, c.mulLadderA.D.z, c.mulLadderA.T.x,
        c.mulLadderA.T.y, c.mulLadderA.T.z] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he ⊢
      rcases he with h | h | h <;> simp [h]
    exact hap d hd' e he' fun h => hrdt d hd (h ▸ he'')
  refine WP.mono (selPtSelf_ok hs₇ (k.testBit (j - 1)) c₇ (n := c.mulLadderA.M.n) (o := c.mulLadderA.R)
    (b := c.mulLadderA.D) hinS
    ⟨hap _ (by simp) _ (by simp) rxy, hap _ (by simp) _ (by simp) rxz, hap _ (by simp) _ (by simp) ryz⟩
    habS)
    fun s₈ ⟨ex₈, ey₈, ez₈, k₈, O₈⟩ => ?_
  have hs₈ := hs₇.of_keepRegs k₈ (by decide)
  have hrbx₈ : s₈.gpr .rbx = BitVec.ofNat 64 (j - 1) := by
    rw [k₈.gpr _ (by decide), k₇.1 _ (by decide), hrbx₆]
  refine WP.mono (testRbx_ok s₈ (by omega_using [hjn, hnb]) hrbx₈) fun s₉ ⟨z₉, k₉⟩ => ⟨?_, z₉⟩
  have hm₉ : s₉.mem = s₈.mem := k₉.2.1
  -- The values.
  have ro₁ : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s₁ x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => by rw [show tmv C c.mulLadderA.M.n base s₁ x = tmv C c.mulLadderA.M.n base s x by
      rw [tmv, tmv, hm₁], hE x hx]
  have ro₂ : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s₂ x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => (tk kp₂ I₁.scr slT (slRo x hx) (roW x hx wT)).trans (ro₁ x hx)
  have ro₃ : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s₃ x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => (tk k₃ hs₂ slDW (slRo x hx) (roW x hx wD)).trans (ro₂ x hx)
  have ro₄ : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s₄ x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => (tk kp₄ hs₃ slR (slRo x hx) (roW x hx wR)).trans (ro₃ x hx)
  have ro₅ : ∀ x ∈ ladRo c.mulLadderA, tmv C c.mulLadderA.M.n base s₅ x = tmv C c.mulLadderA.M.n base s₀ x :=
    fun x hx => (tk kp₅ hs₄ slT (slRo x hx) (roW x hx wT)).trans (ro₄ x hx)
  have r₂ : ∀ x ∈ jacCoords c.mulLadderA.R, tmv C c.mulLadderA.M.n base s₂ x = tmv C c.mulLadderA.M.n base s x :=
    fun x hx => (tk kp₂ I₁.scr slT (slR x hx) (RnT x hx)).trans (by rw [tmv, tmv, hm₁])
  have t₂ : ∀ x ∈ [(c.mulLadderA.T.x, c.mulLadderA.R.x), (c.mulLadderA.T.y, c.mulLadderA.R.y),
      (c.mulLadderA.T.z, c.mulLadderA.R.z)],
      tmv C c.mulLadderA.M.n base s₂ x.1 = tmv C c.mulLadderA.M.n base s x.2 :=
    fun x hx => (tT₂ x hx).trans (by rw [tmv, tmv, hm₁])
  have d₃ : ∀ x ∈ jacCoords c.mulLadderA.D, tmv C c.mulLadderA.M.n base s₃ x =
      runOps (rcb c.mulLadderA.S c.mulLadderA.R c.mulLadderA.T c.mulLadderA.D)
        (tmv C c.mulLadderA.M.n base s₂) x :=
    fun x hx => I₃.val x (List.mem_append_left _ (DinW x hx))
  have r₅ : ∀ x ∈ [(c.mulLadderA.R.x, c.mulLadderA.D.x), (c.mulLadderA.R.y, c.mulLadderA.D.y),
      (c.mulLadderA.R.z, c.mulLadderA.D.z)],
      tmv C c.mulLadderA.M.n base s₅ x.1 = tmv C c.mulLadderA.M.n base s₃ x.2 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (tk kp₅ hs₄ slT (slR _ (by simp [jacCoords])) (RnT _ (by simp [jacCoords]))).trans
        ((I₄.val _ (by simp [jacCoords])).trans e₄.1)
    · exact (tk kp₅ hs₄ slT (slR _ (by simp [jacCoords])) (RnT _ (by simp [jacCoords]))).trans
        ((I₄.val _ (by simp [jacCoords])).trans e₄.2.1)
    · exact (tk kp₅ hs₄ slT (slR _ (by simp [jacCoords])) (RnT _ (by simp [jacCoords]))).trans
        ((I₄.val _ (by simp [jacCoords])).trans e₄.2.2)
  have t₅ : ∀ x ∈ [(c.mulLadderA.T.x, c.mulLadderA.G.x), (c.mulLadderA.T.y, c.mulLadderA.G.y),
      (c.mulLadderA.T.z, c.mulLadderA.G.z)],
      tmv C c.mulLadderA.M.n base s₅ x.1 = tmv C c.mulLadderA.M.n base s₀ x.2 := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact (I₅.val _ (by simp [jacCoords])).trans (e₅.1.trans (ro₄ _ (by simp [ladRo])))
    · exact (I₅.val _ (by simp [jacCoords])).trans (e₅.2.1.trans (ro₄ _ (by simp [ladRo])))
    · exact (I₅.val _ (by simp [jacCoords])).trans (e₅.2.2.trans (ro₄ _ (by simp [ladRo])))
  have d₆ : ∀ x ∈ jacCoords c.mulLadderA.D, tmv C c.mulLadderA.M.n base s₆ x =
      runOps (rcb c.mulLadderA.S c.mulLadderA.R c.mulLadderA.T c.mulLadderA.D)
        (tmv C c.mulLadderA.M.n base s₅) x :=
    fun x hx => I₆.val x (List.mem_append_left _ (DinW x hx))
  have r₆ : ∀ x ∈ jacCoords c.mulLadderA.R, tmv C c.mulLadderA.M.n base s₆ x = tmv C c.mulLadderA.M.n base s₅ x :=
    fun x hx => tk k₆ hs₅ slDW (slR x hx) (RnD x hx)
  have hstep' := hstep (j - 1) (by omega_using [hj, hjn])
    (tmv C c.mulLadderA.M.n base s c.mulLadderA.R.x) (tmv C c.mulLadderA.M.n base s c.mulLadderA.R.y)
    (tmv C c.mulLadderA.M.n base s c.mulLadderA.R.z)
    (tmv C c.mulLadderA.M.n base s₃ c.mulLadderA.D.x) (tmv C c.mulLadderA.M.n base s₃ c.mulLadderA.D.y)
    (tmv C c.mulLadderA.M.n base s₃ c.mulLadderA.D.z)
    (tmv C c.mulLadderA.M.n base s₆ c.mulLadderA.D.x) (tmv C c.mulLadderA.M.n base s₆ c.mulLadderA.D.y)
    (tmv C c.mulLadderA.M.n base s₆ c.mulLadderA.D.z) (by rw [Nat.sub_add_cancel hj]; exact hI.q)
    (by
      simp only [ladDbl, Bool.false_eq_true, ↓reduceIte]
      rw [d₃ _ (by simp [jacCoords]), d₃ _ (by simp [jacCoords]), d₃ _ (by simp [jacCoords]), v₃,
        ro₂ _ (by simp [ladRo]), ro₂ _ (by simp [ladRo]), r₂ _ (by simp [jacCoords]),
        r₂ _ (by simp [jacCoords]), r₂ _ (by simp [jacCoords]), t₂ (c.mulLadderA.T.x, c.mulLadderA.R.x) (by simp), t₂ (c.mulLadderA.T.y, c.mulLadderA.R.y) (by simp),
        t₂ (c.mulLadderA.T.z, c.mulLadderA.R.z) (by simp)])
    (by
      simp only [ladAdd, Bool.false_eq_true, ↓reduceIte]
      rw [d₆ _ (by simp [jacCoords]), d₆ _ (by simp [jacCoords]), d₆ _ (by simp [jacCoords]), v₆,
        ro₅ _ (by simp [ladRo]), ro₅ _ (by simp [ladRo]), r₅ (c.mulLadderA.R.x, c.mulLadderA.D.x) (by simp),
        r₅ (c.mulLadderA.R.y, c.mulLadderA.D.y) (by simp), r₅ (c.mulLadderA.R.z, c.mulLadderA.D.z) (by simp), t₅ (c.mulLadderA.T.x, c.mulLadderA.G.x) (by simp),
        t₅ (c.mulLadderA.T.y, c.mulLadderA.G.y) (by simp), t₅ (c.mulLadderA.T.z, c.mulLadderA.G.z) (by simp)])
  have U₈ : Unch base [(c.mulLadderA.R.x, 8 * c.mulLadderA.M.n), (c.mulLadderA.R.y, 8 * c.mulLadderA.M.n),
      (c.mulLadderA.R.z, 8 * c.mulLadderA.M.n)] s₆.mem s₉.mem := fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hx
    rw [hm₉, O₈ x hx.1 hx.2.1 hx.2.2, hm₇]
  have sel : ∀ {x d : Nat}, wordsVal s₈.mem base x c.mulLadderA.M.n = (if k.testBit (j - 1) then
      wordsVal s₆.mem base d c.mulLadderA.M.n else wordsVal s₆.mem base x c.mulLadderA.M.n) →
      tmv C c.mulLadderA.M.n base s₉ x = if k.testBit (j - 1) then tmv C c.mulLadderA.M.n base s₆ d
        else tmv C c.mulLadderA.M.n base s₆ x := fun {x d} h => by
    show toM _ _ _ = _
    rw [hm₉, h]; split <;> rfl
  rw [hm₇] at ex₈ ey₈ ez₈
  refine ⟨hs₈.of_keeps k₉ (by decide), by rw [k₉.1 _ (by simp), hrbx₈], ⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hr' : r ∉ clob c.mulLadderA.M.n := fun h => hr (mem_powClob_of_clob h)
    have hrb : r ≠ .rbx := fun h => hr (h ▸ List.mem_cons_self ..)
    have hra : r ≠ .rax := fun h => hr' (h ▸ by simp [clob])
    have hrc : r ≠ .rcx := fun h => hr' (h ▸ by simp [clob])
    have hrd : r ≠ .rdx := fun h => hr' (h ▸ by simp [clob])
    rw [k₉.1 r (by simp), k₈.gpr r (by simp [hra, hrd]), k₇.1 r (by simp [hra, hrc]), k₆.gpr r hr',
      kp₅.gpr r hr', kp₄.gpr r hr', k₃.gpr r hr', kp₂.gpr r hr', k₁.1 r (by simp [hrb]), hI.keep.gpr r hr]
  · rw [k₉.2.2.1, k₈.rd, k₇.2.2.1, k₆.rd, kp₅.rd, kp₄.rd, k₃.rd, kp₂.rd, k₁.2.2.1, hI.keep.rd]
  · rw [k₉.2.2.2, k₈.wr, k₇.2.2.2, k₆.wr, kp₅.wr, kp₄.wr, k₃.wr, kp₂.wr, k₁.2.2.2, hI.keep.wr]
  · exact (U₀₆.trans U₈).mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hw
      · exact mem_ladW_R w hw
  · have hM := I₆.mod
    have hmo := hL.lay.mo
    refine ⟨hM.n0, hM.mo, hM.tmp, hM.sep, ?_, hM.inv, hM.red⟩
    rw [U₈.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact (hmo c.mulLadderA.R.x (hSl _ (by simp))).symm
      · exact (hmo c.mulLadderA.R.y (hSl _ (by simp))).symm
      · exact (hmo c.mulLadderA.R.z (hSl _ (by simp))).symm) (by have := hs₆.nowrap; have := hM.mo; omega_using [hn, this])]
    exact hM.val
  · have lD : ∀ x ∈ jacCoords c.mulLadderA.D, wordsVal s₆.mem base x c.mulLadderA.M.n < C.p :=
      fun x hx => I₆.lt x (List.mem_append_left _ (DinW x hx))
    have lR : ∀ x ∈ jacCoords c.mulLadderA.R, wordsVal s₆.mem base x c.mulLadderA.M.n < C.p :=
      fun x hx => I₆.lt x (by simp only [List.mem_append]; exact Or.inr (Or.inr (Or.inl hx)))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm₉, ex₈]; split
      · exact lD _ (by simp [jacCoords])
      · exact lR _ (by simp [jacCoords])
    · rw [hm₉, ey₈]; split
      · exact lD _ (by simp [jacCoords])
      · exact lR _ (by simp [jacCoords])
    · rw [hm₉, ez₈]; split
      · exact lD _ (by simp [jacCoords])
      · exact lR _ (by simp [jacCoords])
  · rw [sel ex₈, sel ey₈, sel ez₈, r₆ c.mulLadderA.R.x (by simp [jacCoords]), r₆ c.mulLadderA.R.y (by simp [jacCoords]),
      r₆ c.mulLadderA.R.z (by simp [jacCoords]), r₅ (c.mulLadderA.R.x, c.mulLadderA.D.x) (by simp), r₅ (c.mulLadderA.R.y, c.mulLadderA.D.y) (by simp),
      r₅ (c.mulLadderA.R.z, c.mulLadderA.D.z) (by simp)]
    exact hstep'

/-- What `mulBodyA` writes: `mulW`'s slots and `EM` (its copy of `Q`'s `y`). -/
abbrev mulWA (c : Cfg) : List (Nat × Nat) :=
  slW c [RX, RY, RZ, ACC, PT, EM, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP] ++
    [(bitsAt c.n 0, 64 * c.n + 8)]

/-- `mulBodyA`: `R = [k]Q`, as `mulBody_ok`, from `p`, zero, one and `a R`
in their slots (it writes `3 b R` itself). -/
theorem mulBodyA_ok (hc : BaseCfgOk c) (hC : Law c.C) (hnc : Mont.callOf c.MP' = none) {base : Addr}
    {s : State} (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a)
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulBodyA.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (mulWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hplt := hc.p_lt
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain hsz : bitsAt c.n 0 + 64 * c.n ≤ size := bitsAt_le c h7 (j := 0) (by decide)
  obtain sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
  obtain ap : ∀ {i j}, i ≠ j → c.sl i ≤ c.sl j ∨ c.sl j + 8 * c.n ≤ c.sl i := fun h => by
    rcases sl_apart c h with h | h <;> omega_arith
  show WP isa (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n))
    (.seq (.block (copy c.n (c.sl ACC) (c.sl RX) ++ copy c.n (c.sl EM) (c.sl RY) ++
      copy c.n (c.sl RX) (c.sl ZERO) ++ copy c.n (c.sl RY) (c.sl ONEP) ++ copy c.n (c.sl RZ) (c.sl ZERO) ++
      setConst c.n (c.sl PT) (c.mont (3 * c.C.b)) ++ [.mov32 .rbx (.imm (BitVec.ofNat 32 (64 * c.n)))]))
      (.loop c.ladderBodyA.inline .ne))) s _
  -- The table of `k`'s bits.
  refine WP.seq (WP.mono (bits_ok hs h0 (by omega_arith) (sz (i := K) (by decide)) hsz
    (Or.inl (by have := sl_below_bits c (i := K) (by decide) 0 0 (.inl (by decide)); omega_arith)))
    fun s₁ ⟨b₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  obtain U₁ : Unch base [(bitsAt c.n 0, 64 * c.n + 8)] s.mem s₁.mem := fun x hx =>
    O₁ x (by have := hx _ (List.mem_singleton_self _); dsimp only at this; omega_arith)
  -- `Q` to `ACC` and `EM`, `R` the point at infinity, `3 b R` to `PT`.
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff, WP.block_append_iff, WP.block_append_iff,
    WP.block_append_iff, WP.block_append_iff]
  refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl ACC) (a := c.sl RX)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₂ (o := c.sl EM) (a := c.sl RY)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₃ ⟨v₃, k₃, O₃⟩ => ?_
  obtain hs₃ := hs₂.of_keepRegs k₃ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₃ (o := c.sl RX) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₄ ⟨v₄, k₄, O₄⟩ => ?_
  obtain hs₄ := hs₃.of_keepRegs k₄ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₄ (o := c.sl RY) (a := c.sl ONEP)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₅ ⟨v₅, k₅, O₅⟩ => ?_
  obtain hs₅ := hs₄.of_keepRegs k₅ (by decide)
  refine WP.mono (copy_ok (size := size) c.n hs₅ (o := c.sl RZ) (a := c.sl ZERO)
    (sz (by decide)) (sz (by decide)) (ap (by decide))) fun s₆ ⟨v₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_keepRegs k₆ (by decide)
  refine WP.mono (setConst_ok hs₆ (n := c.n) (o := c.sl PT) (x := c.mont (3 * c.C.b)) (sz (by decide))
    (by have := hmont (3 * c.C.b); omega_arith)) fun s₇ ⟨v₇, k₇, O₇⟩ => ?_
  obtain hs₇ := hs₆.of_keepRegs k₇ (by decide)
  refine WP.mono (mov32Rbx_ok s₇ (j := 64 * c.n) (by omega_arith)) fun s₈ ⟨b₈, k₈⟩ => ?_
  have hm₈ : s₈.mem = s₇.mem := k₈.2.1
  obtain hs₈ : Scr s₈ base size := hs₇.of_keeps k₈ (by decide)
  -- What each step leaves.
  obtain U₂ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC]) s.mem s₂.mem := U₁.trans O₂.unch
  obtain U₃ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM]) s.mem s₃.mem := U₂.trans O₃.unch
  obtain U₄ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM, RX]) s.mem s₄.mem :=
    U₃.trans O₄.unch
  obtain U₅ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM, RX, RY]) s.mem s₅.mem :=
    U₄.trans O₅.unch
  obtain U₆ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM, RX, RY, RZ]) s.mem s₆.mem :=
    U₅.trans O₆.unch
  obtain U₇ : Unch base ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM, RX, RY, RZ, PT]) s.mem s₈.mem := by
    rw [hm₈]; exact U₆.trans O₇.unch
  obtain U₂₇ : Unch base (slW c [EM, RX, RY, RZ, PT]) s₂.mem s₈.mem := by
    rw [hm₈]; exact (((O₃.unch.trans O₄.unch).trans O₅.unch).trans O₆.unch).trans O₇.unch
  obtain U₃₇ : Unch base (slW c [RX, RY, RZ, PT]) s₃.mem s₈.mem := by
    rw [hm₈]; exact ((O₄.unch.trans O₅.unch).trans O₆.unch).trans O₇.unch
  obtain U₄₇ : Unch base (slW c [RY, RZ, PT]) s₄.mem s₈.mem := by
    rw [hm₈]; exact (O₅.unch.trans O₆.unch).trans O₇.unch
  obtain U₅₇ : Unch base (slW c [RZ, PT]) s₅.mem s₈.mem := by rw [hm₈]; exact O₆.unch.trans O₇.unch
  obtain U₆₇ : Unch base (slW c [PT]) s₆.mem s₈.mem := by rw [hm₈]; exact O₇.unch
  obtain e₁ := fun {i} (hi : i < 45) => sv_unch U₁ h7 hn hi (apart_pad hi)
  obtain acc₈ : sv c base s₈ ACC = sv c base s RX :=
    (sv_unch U₂₇ h7 hn (i := ACC) (by decide) (apart_slW (by decide))).trans (v₂.trans (e₁ (by decide)))
  obtain em₈ : sv c base s₈ EM = sv c base s RY :=
    (sv_unch U₃₇ h7 hn (i := EM) (by decide) (apart_slW (by decide))).trans
      (v₃.trans (sv_unch U₂ h7 hn (i := RY) (by decide) (apart_bits_slW (by decide) (by decide))))
  obtain rx₈ : sv c base s₈ RX = 0 :=
    (sv_unch U₄₇ h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans
      (v₄.trans ((sv_unch U₃ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz))
  obtain one₄ : sv c base s₄ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (sv_unch U₄ h7 hn (i := ONEP) (by decide) (apart_bits_slW (by decide) (by decide))).trans hone
  obtain ry₈ : sv c base s₈ RY = c.mont 1 := by
    obtain h := (sv_unch U₅₇ h7 hn (i := RY) (by decide) (apart_slW (by decide))).trans (v₅.trans one₄)
    rw [show c.mont 1 = 2 ^ (64 * c.n) % c.C.p by show 1 * c.R % c.C.p = _; rw [Nat.one_mul]; rfl]
    exact h
  obtain rz₈ : sv c base s₈ RZ = 0 :=
    (sv_unch U₆₇ h7 hn (i := RZ) (by decide) (apart_slW (by decide))).trans
      (v₆.trans ((sv_unch U₅ h7 hn (i := ZERO) (by decide) (apart_bits_slW (by decide) (by decide))).trans hz))
  obtain pt₈ : sv c base s₈ PT = c.mont (3 * c.C.b) := by
    show wordsVal s₈.mem _ _ _ = _; rw [hm₈]; exact v₇
  obtain e₈ := fun {i} (hi : i < 45) (hl : i ∉ [ACC, EM, RX, RY, RZ, PT]) =>
    sv_unch U₇ h7 hn hi (apart_bits_slW hi hl)
  obtain mp₈ : sv c base s₈ MP = c.C.p := (e₈ (i := MP) (by decide) (by decide)).trans hmp
  obtain ap₈ : sv c base s₈ AP = c.mont c.C.a := (e₈ (i := AP) (by decide) (by decide)).trans hap
  obtain one₈ : sv c base s₈ ONEP = 2 ^ (64 * c.n) % c.C.p :=
    (e₈ (i := ONEP) (by decide) (by decide)).trans hone
  obtain U₂₇' : Unch base (slW c [ACC, EM, RX, RY, RZ, PT]) s₁.mem s₈.mem := by
    rw [hm₈]; exact ((((O₂.unch.trans O₃.unch).trans O₄.unch).trans O₅.unch).trans O₆.unch).trans O₇.unch
  obtain k₈' : ∀ t < 64 * c.n, s₈.mem (off base (bitsAt c.n 0 + t)) =
      if (sv c base s K).testBit t then 1 else 0 := fun t ht => by
    rw [tbl_unch U₂₇' h7 hn (j := 0) (by decide) ht (tbl_apart_slW (by decide) 0 t ht)]
    exact b₁ t ht
  -- The ladder.
  obtain hlt : ∀ x ∈ ladR c.mulLadderA, wordsVal s₈.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, PT, ACC, EM, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₈ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt ap₈ (hmont _)
    · exact lt_of_eq_of_lt pt₈ (hmont _)
    · rw [acc₈]; exact hqx
    · rw [em₈]; exact hqy
    · exact lt_of_eq_of_lt one₈ (Nat.mod_lt _ (by omega_arith))
    · exact lt_of_eq_of_lt rx₈ (by omega_arith)
    · exact lt_of_eq_of_lt ry₈ (hmont _)
    · exact lt_of_eq_of_lt rz₈ (by omega_arith)
  obtain hG : Rep c.C (tmv c.C c.n base s₈ (c.sl ACC)) (tmv c.C c.n base s₈ (c.sl EM))
      (tmv c.C c.n base s₈ (c.sl ONEP)) (ptQ c base s) := by
    show Rep c.C (toM _ _ (sv c base s₈ ACC)) (toM _ _ (sv c base s₈ EM)) (toM _ _ (sv c base s₈ ONEP))
      (Point.affine (toM _ _ (sv c base s RX)) (toM _ _ (sv c base s RY)))
    rw [acc₈, em₈, one₈, toM_one hpR]
    exact rep_affine' hC _ _
  obtain hstep := step_rep' (L := c.mulLadderA) (k := sv c base s K) (a0 := false) hC hQ
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₈ AP) = _; rw [ap₈]; exact toM_cmont hc _)
    (by show toM c.C.p (2 ^ (64 * c.n)) (sv c base s₈ PT) = _; rw [pt₈]; exact toM_cmont hc _) hG
    fun h => absurd h Bool.false_ne_true
  obtain hR : Rep c.C (tmv c.C c.n base s₈ (c.sl RX)) (tmv c.C c.n base s₈ (c.sl RY))
      (tmv c.C c.n base s₈ (c.sl RZ)) (mul (sv c base s K >>> (64 * c.n)) (ptQ c base s)) := by
    show Rep c.C (toM _ _ (sv c base s₈ RX)) (toM _ _ (sv c base s₈ RY)) (toM _ _ (sv c base s₈ RZ)) _
    rw [rx₈, ry₈, rz₈, toM_cmont hc, toM_zero, shiftRight_eq_zero (wordsVal_lt _ _ _ _), mul_zero_pt]
    exact rep_infinity' hC
  have hL := ladLayMA hc
  have hnb := hL.nbits
  refine countLoop_ok (Inv := fun j s' => LadInv c.mulLadderA c.C base size
      (fun j X Y Z => Rep c.C X Y Z (mul (sv c base s K >>> j) (ptQ c base s))) s₈ s' j)
    (n := c.mulLadderA.nbits)
    (fun j s' h1 h2 hi => ladderBodyA_ok hc hpR hnc (fun x hx => hlt x (mem_ladRo_ladR hx))
      hstep k₈' h1 h2 hi)
    (fun s' hi => ⟨?_, ?_, hi.mod, hi.lt, ?_⟩) hnb.1
    ⟨hs₈, b₈, ⟨fun _ _ => rfl, rfl, rfl⟩, Unch.refl _ _ _, modP_of hc mp₈,
      fun x hx => hlt x (List.mem_append_right _ hx), hR⟩
  · obtain hk1 : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
    obtain hk2 : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => hk1 r (by
      simp only [List.mem_singleton] at hr; simp [hr])
    obtain k₈'' : KeepRegs (powClob c.n) s₇ s₈ :=
      ⟨fun r hr => k₈.1 r fun h => hr (hk1 r (by simp only [List.mem_singleton] at h; simp [h])),
        k₈.2.2.1, k₈.2.2.2⟩
    exact (((((((k₁.mono hk1).trans (k₂.mono hk2)).trans (k₃.mono hk2)).trans (k₄.mono hk2)).trans
      (k₅.mono hk2)).trans (k₆.mono hk2)).trans (k₇.mono hk2)).trans (k₈''.trans hi.keep)
  · have U' := hi.unch
    rw [ladWMA_eq] at U'
    obtain hsub : ∀ w ∈ ([(bitsAt c.n 0, 64 * c.n + 8)] ++ slW c [ACC, EM, RX, RY, RZ, PT]) ++
        slW c [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP],
        w ∈ mulWA c := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_right _ hw
        · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
      · exact List.mem_append_left _ (List.map_subset _ (by decide) hw)
    exact Unch.cover (U₇.trans U') fun w hw => ⟨w, hsub w hw, Nat.le_refl _, Nat.le_refl _⟩
  · have R' := hi.q
    rw [Nat.shiftRight_zero] at R'
    exact R'

/-- `mulFnA`: what its body gives (`mulBodyA_ok`), as `mulFn_ok`. -/
theorem mulFnA_ok (hc : BaseCfgOk c) (h4 : c.n = 4 ∨ c.n = 6 ∨ c.n = 8 ∨ c.n = 5) (hC : Law c.C)
    (hnc : Mont.callOf c.MP' = none) {base : Addr} {s : State}
    (hs : Scr s base size)
    (hmp : sv c base s MP = c.C.p) (hz : sv c base s ZERO = 0)
    (hone : sv c base s ONEP = 2 ^ (64 * c.n) % c.C.p)
    (hap : sv c base s AP = c.mont c.C.a)
    (hqx : sv c base s RX < c.C.p) (hqy : sv c base s RY < c.C.p)
    (hQ : onCurve c.C (ptQ c base s) = true) :
    WP isa c.mulFnA.inline s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch base (mulWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
        (tmv c.C c.n base s' (c.sl RZ)) (mul (sv c base s K) (ptQ c base s)) := by
  obtain hkept : ∀ r ∈ Cfg.invKeptX.map Prod.fst, r ∈ powClob c.n := by
    rcases h4 with h | h | h | h <;> rw [h] <;> decide
  show WP isa (.seq (.block _) (.seq c.mulBodyA.inline (.block _))) s _
  refine WP.seq (WP.mono (savesX_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  obtain hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  obtain ev : ∀ i, sv c base s₁ i = sv c base s i := fun i => by
    show wordsVal s₁.mem _ _ _ = wordsVal s.mem _ _ _; rw [m₁]
  obtain eQ : ptQ c base s₁ = ptQ c base s := by
    show Point.affine (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) = _
    rw [ev, ev]
  refine WP.seq (WP.mono (mulBodyA_ok hc hC hnc hs₁ ((ev _).trans hmp) ((ev _).trans hz)
    ((ev _).trans hone) ((ev _).trans hap) (by rw [ev]; exact hqx)
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
  obtain hA : ACC ∈ c.mulBaseSlots := by unfold Cfg.mulBaseSlots; split <;> simp
  intro w hw
  refine ⟨w, ?_, Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact List.mem_append_left _ (List.mem_append_left _ (List.map_subset _ (by decide) hw))
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain key : ∀ i ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
          i = ACC ∨ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by
        decide
      rcases key i hi with rfl | h
      · exact List.mem_append_right _ (List.mem_map_of_mem hA)
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h))
    · exact List.mem_append_left _ (List.mem_append_right _ hw)

/-- The same of `mulAdd`'s (`mulWA`). -/
theorem mulWA_sub :
    ∀ w ∈ slW c [RX, RY] ++ mulWA c, ∃ w' ∈ gWA c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  obtain hA : ACC ∈ c.mulBaseSlots := by unfold Cfg.mulBaseSlots; split <;> simp
  intro w hw
  refine ⟨w, ?_, Nat.le_refl _, Nat.le_refl _⟩
  rcases List.mem_append.mp hw with hw | hw
  · exact List.mem_append_left _ (List.mem_append_left _ (List.map_subset _ (by decide) hw))
  · rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      obtain key : ∀ i ∈ [RX, RY, RZ, ACC, PT, EM, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
          i = ACC ∨ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, EM] := by
        decide
      rcases key i hi with rfl | h
      · exact List.mem_append_right _ (List.mem_map_of_mem hA)
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem h))
    · exact List.mem_append_left _ (List.mem_append_right _ hw)

/-- `R = [k]G` for a secret `k`, after the setup and the tables (but `k`'s
if `vg_<curve>_mul_base` or `vg_<curve>_mul` makes it): by their calls, or
inline (`gMulK_ok`). -/
theorem gMulKCI_ok (hc : BaseCfgOk c) (hmb : MulBaseOkI c) (hC : Law c.C) (hT : CombTbls c) {hs : Option Nat}
    {s₀ : State} (hp : Pre c s₀) {s : State} (hS : St₁ c hs s₀ (s₀.gpr .r8) s c.callsMul) :
    WP isa (gMulKCI c) s fun s' => KeepRegs (powClob c.n) s s' ∧ Unch (s₀.gpr .r8) (gWA c) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem (s₀.gpr .r8) ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem (s₀.gpr .r8) x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RX)) (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RY))
        (tmv c.C c.n (s₀.gpr .r8) s' (c.sl RZ)) (mul (kv c s₀) (G c.C)) := by
  unfold gMulKCI
  cases hm : c.mulBase with
  | some C =>
    obtain ⟨d, hcd, h3⟩ := hmb.1 (by rw [hm]; rfl)
    obtain ⟨hTM, hout⟩ := tbl_of hcd hp hS.rd hS.unch
    rw [← hS.syms] at hTM hout
    show WP isa c.mulBaseFn.inline s _
    refine WP.mono (mulBaseFn_ok hc h3 hC hT hcd hS.scr hS.fixed.mp hS.fixed.zero hTM hout)
      fun s' ⟨g', _, rd', wr', _, U', M', L', R'⟩ => ⟨⟨g', rd', wr'⟩, U', M', L', ?_⟩
    rw [← hS.k]; exact R'
  | none =>
    show WP isa (Cfg.gMulKC c).inline s _
    unfold Cfg.gMulKC
    simp only [hm]
    cases hm₂ : c.mul with
    | none =>
      rw [show c.callsMul = false by simp [Cfg.callsMul, hm, hm₂]] at hS
      exact WP.mono (gMulK_ok hc hC hT hp hS) fun s' ⟨K', U', M', L', R'⟩ =>
        ⟨K', U'.mono fun w hw => List.mem_append_left _ hw, M', L', R'⟩
    | some C =>
      obtain ⟨h4, hnc, hnca⟩ := hmb.2 (by rw [hm₂]; rfl)
      have F := hS.fixed
      have hs := hS.scr
      have h7 := hc.n10
      have hn := hs.nowrap
      have hp3 := hc.p_ge
      obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
      obtain sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
      show WP isa (.seq (.block (copy c.n (c.sl RX) (c.sl GX) ++ copy c.n (c.sl RY) (c.sl GY)))
        (c.mulRun C).inline) s _
      refine WP.seq ?_
      rw [WP.block_append_iff]
      refine WP.mono (copy_ok (size := size) c.n hs (o := c.sl RX) (a := c.sl GX)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RX) (j := GX) (by decide) with h | h <;> omega_arith))
        fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
      obtain hs₁ := hs.of_keepRegs k₁ (by decide)
      refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl RY) (a := c.sl GY)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RY) (j := GY) (by decide) with h | h <;> omega_arith))
        fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
      obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
      obtain U₂ : Unch (s₀.gpr .r8) (slW c [RX, RY]) s.mem s₂.mem := O₁.unch.trans O₂.unch
      obtain e₂ := fun {i} (hi : i < 45) (hl : i ∉ [RX, RY]) => sv_unch U₂ h7 hn hi (apart_slW hl)
      have O₁' : Unch (s₀.gpr .r8) (slW c [RX]) s.mem s₁.mem := O₁.unch
      have O₂' : Unch (s₀.gpr .r8) (slW c [RY]) s₁.mem s₂.mem := O₂.unch
      obtain rx₂ : sv c (s₀.gpr .r8) s₂ RX = c.mont c.C.gx :=
        (sv_unch O₂' h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans (v₁.trans F.gx)
      obtain ry₂ : sv c (s₀.gpr .r8) s₂ RY = c.mont c.C.gy :=
        v₂.trans ((sv_unch O₁' h7 hn (i := GY) (by decide) (apart_slW (by decide))).trans F.gy)
      obtain eG : ptQ c (s₀.gpr .r8) s₂ = G c.C := by
        show Point.affine (toM _ _ (sv c _ s₂ RX)) (toM _ _ (sv c _ s₂ RY)) = Point.affine _ _
        rw [rx₂, ry₂, toM_cmont hc, toM_cmont hc]
      have hk : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr, powClob, clob]
      have k₂' : sv c (s₀.gpr .r8) s₂ K = sv c (s₀.gpr .r8) s K := e₂ (by decide) (by decide)
      unfold Cfg.mulRun
      cases hma : c.mulAdd
      · show WP isa c.mulFn s₂ _
        rw [← Code.inline_of_noCalls (hnc hma)]
        refine WP.mono (mulFn_ok hc h4 hC hs₂ ((e₂ (by decide) (by decide)).trans F.mp)
          ((e₂ (by decide) (by decide)).trans F.zero) ((e₂ (by decide) (by decide)).trans F.onep)
          ((e₂ (by decide) (by decide)).trans F.ap) ((e₂ (by decide) (by decide)).trans F.b3p)
          (lt_of_eq_of_lt rx₂ (hmont _)) (lt_of_eq_of_lt ry₂ (hmont _)) (by rw [eG]; exact hc.onG))
          fun s' ⟨K', U', M', L', R'⟩ => ⟨((k₁.mono hk).trans (k₂.mono hk)).trans K',
            Unch.cover (U₂.trans U') mulW_sub, M', L', by rw [eG, k₂', hS.k] at R'; exact R'⟩
      · show WP isa c.mulFnA.inline s₂ _
        refine WP.mono (mulFnA_ok hc h4 hC (hnca hma) hs₂ ((e₂ (by decide) (by decide)).trans F.mp)
          ((e₂ (by decide) (by decide)).trans F.zero) ((e₂ (by decide) (by decide)).trans F.onep)
          ((e₂ (by decide) (by decide)).trans F.ap)
          (lt_of_eq_of_lt rx₂ (hmont _)) (lt_of_eq_of_lt ry₂ (hmont _)) (by rw [eG]; exact hc.onG))
          fun s' ⟨K', U', M', L', R'⟩ => ⟨((k₁.mono hk).trans (k₂.mono hk)).trans K',
            Unch.cover (U₂.trans U') mulWA_sub, M', L', by rw [eG, k₂', hS.k] at R'; exact R'⟩

end VG.Proof.Ecdsa.X86_64
