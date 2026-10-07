import VerifiedGarbage.Proof.Ecdsa.Arm.Middle

/-!
# ECDSA on 32-bit ARM: the checks, and `s = k⁻¹ (e + r d) mod n`

`checks_ok`: the masks of `d, k ∈ [1, n-1]` and `r ≠ 0` anded into the flag.
`scalarOps_ok`: `r`, `d` and `e` enter Montgomery's form modulo `n`, then
`s = k⁻¹ (e + r d)`, with `k⁻¹ R` in `ACC`, and `s` leaves it.
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- A slot apart from the flag word keeps its number. -/
theorem sv_flag {base : Addr} {m m' : Mem} (h : Outside base (c.sl FLAG) 4 m m') (h0 : 0 < c.n)
    (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32) {i : Nat} (hi : i < 45) (hif : i ≠ FLAG) :
    wordsVal m' base (c.sl i) c.n = wordsVal m base (c.sl i) c.n := by
  have := sl_apart c hif
  have := sl_le c h7 hi
  exact h.wordsVal (by omega) (by omega)

/-- The checks of `d`, `k` and `r`. -/
theorem checks_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hMN : sv c base s MN = c.C.n) :
    WP isa (.block (c.checkRange (c.sl D) ++ c.checkRange (c.sl K) ++ c.checkNonzero (c.sl RR))) s
      fun s' => flagW c base s' = flagW c base s &&&
          mask32 (0 < sv c base s D ∧ sv c base s D < c.C.n) &&&
          mask32 (0 < sv c base s K ∧ sv c base s K < c.C.n) &&& mask32 (sv c base s RR ≠ 0) ∧
        VG.Proof.X25519.Arm.Rest [.r3, .r4, .r5, .r6, .r7, .r8, .r9] s s' ∧ Outside base (c.sl FLAG) 4 s.mem s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  rw [List.append_assoc]
  refine VG.Proof.X25519.Arm.WP.append (checkRange_ok c hs h0 (sl_le c h7 (i := D) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hf) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_rest k₁ (by decide)
  refine VG.Proof.X25519.Arm.WP.append (checkRange_ok c hs₁ h0 (sl_le c h7 (i := K) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hf) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.mono (checkNonzero_ok c hs₂ h0 (sl_le c h7 (i := RR) (by decide)) hf)
    fun s₃ ⟨f₃, k₃, O₃⟩ => ⟨?_, (k₁.trans k₂).trans (k₃.mono (by simp)), O₁.trans (O₂.trans O₃)⟩
  have e₁ : ∀ i, i < 45 → i ≠ FLAG → wordsVal s₁.mem base (c.sl i) c.n = sv c base s i :=
    fun i hi hif => sv_flag O₁ h0 h7 hn hi hif
  have e₂ : ∀ i, i < 45 → i ≠ FLAG → wordsVal s₂.mem base (c.sl i) c.n = sv c base s i :=
    fun i hi hif => (sv_flag O₂ h0 h7 hn hi hif).trans (e₁ i hi hif)
  have hMN' : wordsVal s.mem base (c.sl MN) c.n = c.C.n := hMN
  rw [f₃, f₂, f₁, e₂ RR (by decide) (by decide), e₁ K (by decide) (by decide),
    e₁ MN (by decide) (by decide), hMN', hMN]

theorem scalar_eq (c : Cfg) : c.scalar =
    .seq (Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM))
    (.seq (Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM))
    (.seq (Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT))
    (.seq (Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))
    (.block (c.checkNonzero (c.sl SS) ++ c.finish)))))))) := rfl

/-- What `scalar`'s field operations leave. -/
structure ScPost (c : Cfg) (base : Addr) (s s' : State) : Prop where
  scr : Scr s' base size
  rest : VG.Proof.X25519.Arm.Rest Mont.callClob s s'
  unch : Unch base (slW c [RM, DM, EM, TT, SM, SS, TMP] ++ [(c.wk, 64 * c.n)]) s.mem s'.mem
  ss_lt : sv c base s' SS < c.C.n
  ss : Fin.ofNat c.C.n (sv c base s' SS) = toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
    (Fin.ofNat c.C.n (sv c base s E) + Fin.ofNat c.C.n (sv c base s RR) * Fin.ofNat c.C.n (sv c base s D))

/-- The first three multiplications by `R² mod n`. -/
theorem scalarIn_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hMN : ModOkW c.MN' size c.C.n s.mem base)
    (hr2 : sv c base s R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n) {rest : Prog isa}
    {Q : State → Prop}
    (h : ∀ s', Scr s' base size → ModOkW c.MN' size c.C.n s'.mem base →
      VG.Proof.X25519.Arm.Rest Mont.callClob s s' →
      Unch base (slW c [RM, DM, EM, TT, SM, SS, TMP] ++ [(c.wk, 64 * c.n)]) s.mem s'.mem →
      sv c base s' RM < c.C.n → sv c base s' DM < c.C.n → sv c base s' EM < c.C.n →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' RM) = Fin.ofNat c.C.n (sv c base s RR) →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' DM) = Fin.ofNat c.C.n (sv c base s D) →
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s' EM) = Fin.ofNat c.C.n (sv c base s E) →
      WP isa rest s' Q) :
    WP isa (.seq ((Mont.mulCall c.SN (c.sl RM) (c.sl RR) (c.sl R2N)))
      (.seq ((Mont.mulCall c.SN (c.sl DM) (c.sl D) (c.sl R2N)))
      (.seq ((Mont.mulCall c.SN (c.sl EM) (c.sl E) (c.sl R2N))) rest))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have hr2lt : sv c base s R2N < c.C.n := by rw [hr2]; exact Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs hf (o := RM) (a := RR) (b := R2N) (by decide) (by decide) (by decide) hr2lt) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hf₁ := hf.of_rest k₁.rest
  have kN₁ := hMN.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have r₁ : sv c base s₁ R2N = sv c base s R2N := sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have d₁ : sv c base s₁ D = sv c base s D := sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  have E₁ : sv c base s₁ E = sv c base s E := sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs₁ hf₁ (o := DM) (a := D) (b := R2N) (by decide) (by decide) (by decide) (by rw [r₁]; exact hr2lt)) fun s₂ ⟨k₂, lt₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have hf₂ := hf₁.of_rest k₂.rest
  have kN₂ := kN₁.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have r₂ : sv c base s₂ R2N = sv c base s R2N :=
    (sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)).trans r₁
  have E₂ : sv c base s₂ E = sv c base s E :=
    (sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)).trans E₁
  have rm₂ : sv c base s₂ RM = sv c base s₁ RM := sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs₂ hf₂ (o := EM) (a := E) (b := R2N) (by decide) (by decide) (by decide) (by rw [r₂]; exact hr2lt)) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  have rm₃ : sv c base s₃ RM = sv c base s₁ RM :=
    (sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)).trans rm₂
  have dm₃ : sv c base s₃ DM = sv c base s₂ DM := sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)
  refine h s₃ (k₃.scr hs₂) (kN₂.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide))
    ((k₁.rest.trans k₂.rest).trans k₃.rest) ?_ (by rw [rm₃]; exact lt₁) (by rw [dm₃]; exact lt₂) lt₃
    (by rw [rm₃, toM_r2 hnR (by rw [e₁, hr2])])
    (by rw [dm₃, toM_r2 hnR (by rw [e₂, r₁, hr2]), d₁])
    (by rw [toM_r2 hnR (by rw [e₃, r₂, hr2]), E₂])
  exact ((unch_slots (MN'_n c) rfl k₁.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)).trans
    ((unch_slots (MN'_n c) rfl k₂.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)).trans
    (unch_slots (MN'_n c) rfl k₃.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)))).mono fun w hw => by
      simpa only [List.mem_append, or_self] using hw

/-- The rest of the field operations: `s`, left Montgomery's form. -/
theorem scalarOut_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hMN : ModOkW c.MN' size c.C.n s.mem base) (hone : sv c base s ONE = 1)
    (hdm : sv c base s DM < c.C.n) (hem : sv c base s EM < c.C.n)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Scr s' base size → VG.Proof.X25519.Arm.Rest Mont.callClob s s' →
      Unch base (slW c [RM, DM, EM, TT, SM, SS, TMP] ++ [(c.wk, 64 * c.n)]) s.mem s'.mem →
      sv c base s' SS < c.C.n →
      Fin.ofNat c.C.n (sv c base s' SS) = toM c.C.n (2 ^ (64 * c.n)) (sv c base s ACC) *
        (toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM) * toM c.C.n (2 ^ (64 * c.n)) (sv c base s DM) +
          toM c.C.n (2 ^ (64 * c.n)) (sv c base s EM)) →
      WP isa rest s' Q) :
    WP isa (.seq ((Mont.mulCall c.SN (c.sl TT) (c.sl RM) (c.sl DM)))
      (.seq (Mont.addCall c.SN (c.sl TT) (c.sl TT) (c.sl EM))
      (.seq ((Mont.mulCall c.SN (c.sl SM) (c.sl ACC) (c.sl TT)))
      (.seq ((Mont.mulCall c.SN (c.sl SS) (c.sl SM) (c.sl ONE))) rest)))) s Q := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs hf (o := TT) (a := RM) (b := DM) (by decide) (by decide) (by decide) hdm) fun s₁ ⟨k₁, lt₁, e₁⟩ => ?_)
  have hs₁ := k₁.scr hs
  have hf₁ := hf.of_rest k₁.rest
  have kN₁ := hMN.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₁ (by decide) (by decide)
  have em₁ : sv c base s₁ EM = sv c base s EM := sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)
  refine WP.seq (WP.mono (slAdd_ok hc.fn (MN'_n c) h7 hs₁ hf₁ (o := TT) (a := TT) (b := EM) (by decide) (by decide) (by decide) (by rw [em₁]; omega)) fun s₂ ⟨k₂, e₂⟩ => ?_)
  have hs₂ := k₂.scr hs₁
  have hf₂ := hf₁.of_rest k₂.rest
  have kN₂ := kN₁.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  have acc₂ : sv c base s₂ ACC = sv c base s ACC := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide)]
  have one₂ : sv c base s₂ ONE = 1 := by
    rw [sv_keep (MN'_n c) rfl h7 hn k₂ (by decide) (by decide) (by decide),
      sv_keep (MN'_n c) rfl h7 hn k₁ (by decide) (by decide) (by decide), hone]
  have tt₂ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₂ TT) =
      toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM) * toM c.C.n (2 ^ (64 * c.n)) (sv c base s DM) +
        toM c.C.n (2 ^ (64 * c.n)) (sv c base s EM) := by
    rw [e₂, toM_add, toM_mul hnR e₁, em₁]
  have ttlt : sv c base s₂ TT < c.C.n := by rw [e₂]; exact Nat.mod_lt _ (by omega)
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs₂ hf₂ (o := SM) (a := ACC) (b := TT) (by decide) (by decide) (by decide) ttlt) fun s₃ ⟨k₃, _, e₃⟩ => ?_)
  have hs₃ := k₃.scr hs₂
  have hf₃ := hf₂.of_rest k₃.rest
  have kN₃ := kN₂.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₃ (by decide) (by decide)
  have one₃ : sv c base s₃ ONE = 1 :=
    (sv_keep (MN'_n c) rfl h7 hn k₃ (by decide) (by decide) (by decide)).trans one₂
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs₃ hf₃ (o := SS) (a := SM) (b := ONE) (by decide) (by decide) (by decide) (by omega)) fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  refine h s₄ (k₄.scr hs₃) ((k₁.rest.trans k₂.rest).trans (k₃.rest.trans k₄.rest)) ?_ lt₄ ?_
  · exact (((unch_slots (MN'_n c) rfl k₁.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₂.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp))).trans
      ((unch_slots (MN'_n c) rfl k₃.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₄.unchOne (l := [RM, DM, EM, TT, SM, SS, TMP]) (by simp) (by simp)))).mono fun w hw => by
        simpa only [List.mem_append, or_self] using hw
  · rw [toM_one_mul hnR (by rw [e₄, one₃]), toM_mul hnR e₃, acc₂, tt₂]

end VG.Proof.Ecdsa.Arm
