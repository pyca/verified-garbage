import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.Scalars

namespace VG.Proof.Ecdsa.Verify.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdh.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- The checks of `r` and `s`, `w = s^(n-2)`, `u` and `v`. -/
theorem mid_with_inverse_ok (hc : CfgOk c)
    (inverse : Prog isa) (rs : List Reg) (W : List (Nat × Nat))
    (h0r : Reg.x0∉rs) (hfixed : FixedOk c W)
    (hsep : ∀ {i},i<45 → i∉[ACC,TMP] → ∀ w∈W,
      c.sl i+8*c.n≤w.1 ∨ w.1+w.2≤c.sl i)
    (hbound : ∀ w∈W,w.1+w.2≤size)
    (hinverse : ∀ {s : State} {base : Addr},Scr s base size →
      ModOkA c.MN' size c.C.n s.mem base → wordsVal s.mem base (c.sl KM) c.n<c.C.n →
      WP isa inverse s fun t => KeepRegs rs s t ∧ Unch base W s.mem t.mem ∧
        wordsVal t.mem base (c.sl ACC) c.n<c.C.n ∧
        toM c.C.n (2^(64*c.n)) (wordsVal t.mem base (c.sl ACC) c.n)=
          toM c.C.n (2^(64*c.n)) (wordsVal s.mem base (c.sl KM) c.n)^(c.C.n-2)) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hF : Front c s₀ base g s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Mid c s₀ base g s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.scalars c) (.seq inverse
      (.seq (Impl.Ecdsa.Verify.AArch64.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have F := hF.fixed
  have hf : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have hr2lt : ∀ {m : Mem}, wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n →
      wordsVal m base (c.sl R2N) c.n < c.C.n := fun h => by rw [h]; exact Nat.mod_lt _ (by omega)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  rw [WP.block_append_iff]
  refine WP.mono_syms (checkRange_ok c hF.scr h0 (sl_le c h7 (i := K) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c K) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₁ ⟨f₁, k₁, O₁⟩ sy₁ => ?_
  have hs₁ := hF.scr.of_keepRegs k₁ (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono_syms (checkRange_ok c hs₁ h0 (sl_le c h7 (i := PT) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf (sl_mod8 c PT) (sl_mod8 c MN) (sl_mod8 c FLAG)) fun s₂ ⟨f₂, k₂, O₂⟩ sy₂ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  have v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (v₁ hi hf)
  have U₂ : Unch base [(c.sl FLAG, 8)] s.mem s₂.mem := by
    have := O₁.unch.trans O₂.unch
    exact this.mono fun w hw => by simpa using hw
  have F₂ := F.unch h7 hn fixedOk_flag U₂
  have flag₂ : word s₂.mem base (c.sl FLAG) =
      mask (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := F.mn
    have hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ := (v₁ (by decide) (by decide)).trans hF.pt
    have hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := (v₁ (by decide) (by decide)).trans F.mn
    rw [f₂, f₁, hF.flag, mask_and, mask_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono_syms (mulN_ok hc hs₂ (modN_of hc F₂.mn) (o := SM') (a := PT) (b := R2N) (by decide) (by decide)
    (by decide) (hr2lt F₂.r2n) (by decide)) fun s₃ ⟨hs₃, M₃, g₃, rd₃, wr₃, U₃, v₃, lt₃, e₃⟩ sy₃ => ?_
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from F₂.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (WP.mono_syms (hinverse hs₃ M₃ lt₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ sy₄ => ?_)
  have hs₄ := hs₃.of_keepRegs K₄ h0r
  have F₄ := F₃.unch h7 hn hfixed U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (hsep hi hl)
  have w₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact v₄
  -- `u` and `v`.
  rw [uv_eq]
  refine WP.seq ?_
  refine WP.seq (WP.mono_syms (mulN_ok hc hs₄ (modN_of hc F₄.mn) (o := EM') (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₄.r2n) (by decide)) fun s₅ ⟨hs₅, M₅, g₅, rd₅, wr₅, U₅, v₅, lt₅, e₅⟩ sy₅ => ?_)
  have F₅ := F₄.unch h7 hn (fixedOk_slW (by decide)) U₅
  refine WP.seq (WP.mono_syms (mulN_ok hc hs₅ M₅ (o := RM') (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₅.r2n) (by decide)) fun s₆ ⟨hs₆, M₆, g₆, rd₆, wr₆, U₆, v₆, lt₆, e₆⟩ sy₆ => ?_)
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide) (by decide), v₅ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono_syms (mulN_ok hc hs₆ M₆ (o := UM) (a := EM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄) (by decide)) fun s₇ ⟨hs₇, M₇, g₇, rd₇, wr₇, U₇, v₇, lt₇, e₇⟩ sy₇ => ?_)
  have F₇ := F₆.unch h7 hn (fixedOk_slW (by decide)) U₇
  have acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by
    rw [v₇ (by decide) (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono_syms (mulN_ok hc hs₇ M₇ (o := VM) (a := RM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄) (by decide))
    fun s₈ ⟨hs₈, M₈, g₈, rd₈, wr₈, U₈, v₈, lt₈, e₈⟩ sy₈ => ?_)
  have F₈ := F₇.unch h7 hn (fixedOk_slW (by decide)) U₈
  refine WP.seq (WP.mono_syms (mulN_ok hc hs₈ M₈ (o := U) (a := UM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from F₈.one]; omega) (by decide))
    fun s₉ ⟨hs₉, M₉, g₉, rd₉, wr₉, U₉, v₉, lt₉, e₉⟩ sy₉ => ?_)
  have F₉ := F₈.unch h7 hn (fixedOk_slW (by decide)) U₉
  refine WP.mono_syms (mulN_ok hc hs₉ M₉ (o := V) (a := VM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from F₉.one]; omega) (by decide))
    fun s₁₀ ⟨hs₁₀, M₁₀, g₁₀, rd₁₀, wr₁₀, U₁₀, v₁₀, lt₁₀, e₁₀⟩ sy₁₀ => h s₁₀ ?_
  have F₁₀ := F₉.unch h7 hn (fixedOk_slW (by decide)) U₁₀
  -- What changed: the flag and `midW`.
  have UW : Unch base ([(c.sl FLAG, 8)] ++ W ++ slW c midW) s.mem s₁₀.mem := by
    refine (U₂.trans (U₃.trans (U₄.trans (U₅.trans (U₆.trans (U₇.trans (U₈.trans (U₉.trans
      U₁₀)))))))).mono fun w hw => ?_
    simp only [List.mem_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hw ⊢
    grind
  have hmw : ∀ i, i ∉ midW → i ∉ [ACC, TMP] := fun i hl h => hl (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> decide)
  have a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun hi hl hf =>
    sv_unch UW h7 hn hi (apart_append (apart_append (apart_flag h0 hf) (hsep hi (hmw _ hl)))
      (apart_slW hl))
  -- The values.
  have d₄ : sv c base s₄ D = dig c s₀ >>> c.sh := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  have k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  have em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀ >>> c.sh) := by
    rw [v₆ (i := EM') (by decide) (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from F₄.r2n]), d₄]
  have rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from F₅.r2n]),
      v₅ (i := K) (by decide) (by decide) (by decide), k₄]
  have um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀ >>> c.sh) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄]
  have vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide) (by decide), rm₆, acc₇, w₄]
  have U' : Unch base (W ++ slW c midW) s₂.mem s₁₀.mem := by
    refine (U₃.trans (U₄.trans (U₅.trans (U₆.trans (U₇.trans (U₈.trans (U₉.trans
      U₁₀))))))).mono fun w hw => ?_
    simp only [List.mem_append, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hw ⊢
    grind
  refine ⟨hs₁₀, by rw [wr₁₀, wr₉, wr₈, wr₇, wr₆, wr₅, K₄.wr, wr₃, k₂.wr, k₁.wr, hF.wr],
    by rw [rd₁₀, rd₉, rd₈, rd₇, rd₆, rd₅, K₄.rd, rd₃, k₂.rd, k₁.rd, hF.rd], F₁₀,
    by rw [a (i := RX) (by decide) (by decide) (by decide), hF.rx],
    by rw [a (i := RY) (by decide) (by decide) (by decide), hF.ry],
    by rw [a (i := RZ) (by decide) (by decide) (by decide), hF.rz], ?_,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px_lt,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py_lt,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py,
    by rw [v₁₀ (by decide) (by decide) (by decide), v₉ (by decide) (by decide) (by decide),
      v₈ (by decide) (by decide) (by decide), v₇ (by decide) (by decide) (by decide)]; exact lt₆,
    by rw [v₁₀ (by decide) (by decide) (by decide), v₉ (by decide) (by decide) (by decide),
      v₈ (by decide) (by decide) (by decide), v₇ (by decide) (by decide) (by decide), rm₆],
    by rw [v₁₀ (by decide) (by decide) (by decide)]; exact lt₉,
    by rw [v₁₀ (i := U) (by decide) (by decide) (by decide),
      toM_one_mul hnR (by rw [e₉, show sv c base s₈ ONE = 1 from F₈.one]), um₈],
    lt₁₀,
    by rw [toM_one_mul hnR (by rw [e₁₀, show sv c base s₉ ONE = 1 from F₉.one]),
      v₉ (i := VM) (by decide) (by decide) (by decide), vm₈], ?_,
    by rw [sy₁₀, sy₉, sy₈, sy₇, sy₆, sy₅, sy₄, sy₃, sy₂, sy₁, hF.syms],
    by rw [a (i := K) (by decide) (by decide) (by decide), hF.k]⟩
  · have he : word s₁₀.mem base (c.sl FLAG)=word s₂.mem base (c.sl FLAG) := by
      apply U'.word
      · intro w hw
        have h := apart_append (hsep (i:=FLAG) (by decide) (by decide))
          (apart_slW (c:=c) (l:=midW) (i:=FLAG) (by decide)) w hw
        rcases h with h | h
        · exact Or.inl (by omega)
        · exact Or.inr h
      · have := sl_le c h7 (i:=FLAG) (by decide); omega
    rw [he]
    exact flag₂
  · refine unch_whole (hF.unch.trans UW) fun w hw => ?_
    simp only [List.mem_append] at hw
    rcases hw with hw | (hw | hw) | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_of_eq (Nat.zero_add _)
    · exact flag_le h0 h7 w hw
    · exact hbound w hw
    · exact slW_le h7 (by decide) w hw

end VG.Proof.Ecdsa.Verify.AArch64
