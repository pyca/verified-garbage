import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.NafWindowTiming
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombOut
import VerifiedGarbage.Proof.Weierstrass.AArch64.JacCombSum

namespace VG.Proof.Ecdsa.Verify.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V UX UY UZ)
variable {c : Cfg}

theorem jacPoints_ok (hc : CfgOk c) (hn4 : c.n=4) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hM : Mid c s₀ base g s) {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    (hC : Law c.C) (hT : CombOkW c.C Cfg.combW (Cfg.combJ c.n) c.tbl c.start)
    (hTP : TblPre c s₀ (s₀.syms c.tsym) base)
    (hQ₁ : ∀ X Y Z, Rep c.C X Y Z (mul (sv c base s U) (G c.C)) → Q₁ 0 X Y Z)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hQ₂ : ∀ X Y Z, Rep c.C X Y Z (mul (sv c base s V) P) → Q₂ 0 X Y Z)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base g Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.jacPoints c) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt c.n 0, 64 * c.n)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
    fun hi => apart_tbl hi 0 h7
  rw [Impl.Ecdsa.Verify.AArch64.Cfg.jacPoints]
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le c h7 (i := U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := U) (by decide)) (by have := bitsAt0_le c h7; omega) (Or.inl (by have := sl_below_bits c (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt c.n 0, 64 * c.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv c base s₁ i = sv c base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G`.
  obtain ⟨hTM, hout⟩ := tbl_of hTP hM.rd hM.unch
  have hTM₁ : TblMem s₁ (s₀.syms c.tsym) c.combWords :=
    TblMem.of_unch hTM (by rw [k₁.rd, k₁.wr]) U₁ (fun w hw => by
      rw [List.mem_singleton.mp hw]; exact tbl_le h7) hout
  have hF : TCombFixed c.combCfg c.C base size s₁ (sv c base s U) (s₀.syms c.tsym) c.combWords := by
    refine ⟨?_, ?_, ?_, F₁.zero, ?_, wordsVal_lt _ _ _ _, by rw [sy₁, hM.syms]; rfl, hTM₁, hout⟩
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl AP) c.n) = _
      rw [F₁.ap]; exact toM_cmont hc _
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₁.mem base (c.sl BM) c.n) = _
      rw [F₁.bm]; exact toM_cmont hc _
    · intro x hx
      simp only [combRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · show wordsVal s₁.mem base (c.sl AP) c.n < _; rw [F₁.ap]; exact hmont _
      · show wordsVal s₁.mem base (c.sl BM) c.n < _; rw [F₁.bm]; exact hmont _
      · show wordsVal s₁.mem base (c.sl ZERO) c.n < _; rw [F₁.zero]; omega
    · intro t ht
      show s₁.mem (off base (bitsAt c.n 0 + t)) = _
      rw [b₁ t ht]
  have WC := jacComb_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.onG (tcombVals hc.toBaseCfgOk hC hT) hc.p_lt hn4
    (jacComb_sum_ok (tcombLay hc.toBaseCfgOk) (combA hc.toBaseCfgOk) hC hc.am3 hpR hn4 (hmont 1)) hs₁
    (modP_of hc F₁.mp) hF
  refine WP.seq (WP.mono WC fun s₂ h₂ => ?_)
  obtain ⟨K₂, U₂, M₂, L₂, R₂⟩ := h₂
  have q₂ := hQ₁ _ _ _ R₂
  have F₂ := F₁.unch h7 hn fixedOk_tcombW U₂
  rw [tcombW_eq] at U₂
  have hs₂ := hs₁.of_keepRegs K₂ (x0_not_tcombClob hc.n10)
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₂ : ∀ i ∈ [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
      i ∈ ptsW := by decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_append (apart_slW (fun h => hl (sub₂ _ h))) (apart_zw hi)))).trans (v₁ hi)
  -- `[v]Q`.
  have tv₃ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _)
      rw [W₃ hi hl]
  refine jacWinMul_ok hc hn4 hC hs₃ F₃ hP (by rw [W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [tv₃ (by decide) (by decide), tv₃ (by decide) (by decide), tv₃ (by decide) (by decide)]
        exact hrep) fun s₅ W => ?_
  have hs₅ := W.scr
  have F₅ := F₃.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
  have nw : ∀ i < 45, i ∉ ptsW → i ∉ otherI ++ jacTblI ++ [TMP] := by decide
  have v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₅ i = sv c base s₃ i := fun hi hl =>
    sv_unch W.unch h7 hn hi (apart_append (apart_winX hi) (apart_slW (nw _ hi hl)))
  have q₅ := hQ₂ _ _ _ (by rw [← W₃ (i := V) (by decide) (by decide)]; exact W.q)
  -- The sum.
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact sv_unch W.unch h7 hn (by decide) (apart_append (apart_winX (by decide)) (apart_slW (by decide)))
  refine WP.mono (sum_ok hc hs₅ W.mod (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.bm (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact W.lt _ (List.mem_cons_self ..)
    · exact W.lt _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact W.lt _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have v₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₆ i = sv c base s i := fun hi hl =>
    (sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))).trans ((v₅ hi hl).trans (W₃ hi hl))
  have sub₅ : ∀ i ∈ otherI ++ jacTblI ++ [TMP], i ∈ ptsW ++ jacTblI := by decide
  have UW : Unch base ([(bitsAt c.n 0, 64 * c.n), (bitsAt c.n 0 + 64 * c.n, 8 * c.combCfg.zw)] ++
      winX c ++ slW c (ptsW ++ jacTblI)) s.mem s₆.mem := by
    refine (U₁.trans (U₂.trans (U₃.trans (W.unch.trans U₆)))).mono fun w hw => ?_
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | (hw | hw) | hw | (hw | hw) | hw
    · exact Or.inl (Or.inl (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hw))))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₂ i hi)))
    · exact Or.inl (Or.inl (List.mem_cons_of_mem _ hw))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₃ i hi)))
    · exact Or.inl (Or.inr hw)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact Or.inr (List.mem_map_of_mem (sub₅ i hi))
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact Or.inr (List.mem_map_of_mem (List.mem_append_left _ (sub₆ i hi)))
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  have tR₅ : ∀ {i}, i ∈ [AP, BM] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), W₃ (by decide) (by decide)]
  have hb : tmv c.C c.n base s (c.sl BM) = Fin.ofNat c.C.p c.C.b := by
    show toM _ _ (wordsVal s.mem base (c.sl BM) c.n) = _
    rw [F.bm]; exact toM_cmont hc _
  refine ⟨hs₆, by rw [wr₆, W.wr, k₃.wr, K₂.wr, k₁.wr, hM.wr],
    by rw [rd₆, W.rd, k₃.rd, K₂.rd, k₁.rd, hM.rd], F₆, ?_,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm, rz₆.1,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, tR₅ (by decide), hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃, rcbAdd3_eq, ← hc.am3,
        ← ofNat_three_mul]
      rfl⟩, ?_, by rw [v₆ (by decide) (by decide)]; exact hM.k, rz₆.2⟩
  · rw [UW.word (fun w hw => ?_) (by have := sl_le c h7 (i := FLAG) (by decide); omega)]
    · exact hM.flag
    · simp only [List.mem_append] at hw
      rcases hw with (hw | hw) | hw
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        have := sl_below_bits c (i := FLAG) (by decide) 0 0
        rcases hw with rfl | rfl <;> exact Or.inl (by dsimp only; omega)
      · exact (apart_winX (c := c) (i := FLAG) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega)) (fun h => Or.inr h)
      · exact (apart_slW (c := c) (i := FLAG) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact tbl_le h7
      · have := (tcombLay hc.toBaseCfgOk).bits; exact this
    · simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
      have := sl_le' c h7 (i := WT) (by decide)
      have e1 : c.sl WK + 16 * c.n ≤ c.sl WT := by simp (disch := decide) only [sl_eq]; unfold WK WT; omega
      have e2 : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
        simp (disch := decide) only [sl_eq]; unfold WB WT
        have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega
        omega
      rcases hw with rfl | rfl
      · show c.sl WK + 16 * c.n ≤ size; omega
      · show c.sl WB + 64 * (c.n + 1) ≤ size; omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hb := (show ∀ i∈ptsW++jacTblI,i<136 by decide) i hi
      change c.sl i+8*c.n≤size
      rw [sl_eq4 c (Nat.le_of_eq hn4), hn4]; change 64+32*i+32≤8192; omega

end VG.Proof.Ecdsa.Verify.AArch64
