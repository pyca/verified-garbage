module

import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86_64.TCombJP
import VerifiedGarbage.Proof.Ecdsa.X86_64.CombLays
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
public import VerifiedGarbage.Proof.Weierstrass.X86_64.TComb
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
public import VerifiedGarbage.Proof.Weierstrass.X86_64.Ladder
public import VerifiedGarbage.Proof.Weierstrass.Law

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

/-- What a call of `vg_<curve>_mul_base` or `vg_<curve>_mul` needs of the
curve: for the first, a comb and at least three words (so that its slots
hold the six callee-saved registers); for the second, four words (which it
keeps the six registers in `xmm` registers for, as the inversions); and
products written out (the functions call no other). -/
def MulBaseOk (c : Cfg) : Prop :=
  (c.mulBase.isSome = true → ∃ d, c.comb = some d ∧ 3 ≤ c.n ∧ c.mulBaseFn.noCalls = true) ∧
    (c.mul.isSome = true → (c.n = 4 ∨ c.n = 6 ∨ c.n = 8) ∧ c.mulFn.noCalls = true)

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
