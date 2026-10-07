import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front

/-!
# ECDSA verification on 32-bit ARM: `u` and `v`

As on x86 (`Proof/Ecdsa/Verify/X86/Scalars.lean`).

`mid_ok`: from what `front_ok` leaves, `scalars` ands the masks of `r` and
`s` in `[1, n-1]` into the flag and computes `s R mod n`, the signature's
power modulo `n` gives `w = s^(n-2)` (in Montgomery form), and `uv` computes
`r R mod n` (`RM'`) and `u = e w` and `v = r w` modulo `n`, out of
Montgomery's form (`U`, `V`), with the multiplications of `Proof/Mont`.
-/

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (PX PY)
open VG.Impl.Ecdsa.Verify.Arm (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- The slots `mid_ok` writes. -/
abbrev midW : List Nat := [SM', TMP, ACC, PT, EM', RM', UM, VM, U, V]

/-- After `u` and `v`. -/
structure Mid (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  rest : Rest (.lr :: work) s₀ s
  fixed : Fixed c base s₀.gpr s.mem
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  px_lt : sv c base s PX < c.C.p
  py_lt : sv c base s PY < c.C.p
  px : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PX) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyX c s₀) else Fin.ofNat c.C.p c.C.gx
  py : toM c.C.p (2 ^ (64 * c.n)) (sv c base s PY) =
    if KeyOk c s₀ then Fin.ofNat c.C.p (keyY c s₀) else Fin.ofNat c.C.p c.C.gy
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  u_lt : sv c base s U < c.C.n
  u : Fin.ofNat c.C.n (sv c base s U) =
    Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2)
  v_lt : sv c base s V < c.C.n
  v : Fin.ofNat c.C.n (sv c base s V) =
    Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2)
  unch : Unch base [(0, 8192)] s₀.mem s.mem

theorem scalars_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.scalars c =
    .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
      (Mont.mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N)) := rfl

theorem uv_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.uv c =
    .seq (Mont.mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N))
    (.seq (Mont.mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC))
    (.seq (Mont.mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC))
    (.seq (Mont.mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE))
      (Mont.mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)))))) := rfl

/-- One multiplication modulo `n`, on numbered slots: it keeps the modulus and
every other slot but the temporary area's. -/
theorem mulN_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hMN : ModOkW c.MN' size c.C.n s.mem base) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hB : sv c base s b < c.C.n) (hoN : o ≠ MN) :
    WP isa (Mont.mulCall c.SN (c.sl o) (c.sl a) (c.sl b)) s fun s' =>
      Scr s' base size ∧ ModOkW c.MN' size c.C.n s'.mem base ∧
      Rest Mont.callClob s s' ∧
      Unch base (slWk c [o, TMP]) s.mem s'.mem ∧
      (∀ {i}, i < 45 → i ≠ o → i ≠ TMP → sv c base s' i = sv c base s i) ∧
      sv c base s' o < c.C.n ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.n = sv c base s a * sv c base s b % c.C.n := by
  have h7 := hc.n10
  have hn := hs.nowrap
  exact WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs hf ho ha hb hB) fun s' ⟨k, lt, e⟩ =>
    ⟨k.scr hs, hMN.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k (Ne.symm hoN) (by decide),
      k.rest, unch_slots (MN'_n c) rfl k.unchOne (l := [o, TMP]) (by simp) (by simp),
      fun hi h₁ h₂ => sv_keep (MN'_n c) rfl h7 hn k hi h₁ h₂, lt, e⟩

/-- The checks of `r` and `s`, `w = s^(n-2)`, `u` and `v`. -/
theorem mid_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hF : Front c s₀ base s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Mid c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.Arm.Cfg.scalars c) (.seq (pow c.powN c.SN)
      (.seq (Impl.Ecdsa.Verify.Arm.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.scr.nowrap
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have F := hF.fixed
  have hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega
  have henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  have hr2lt : ∀ {m : Mem}, wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n →
      wordsVal m base (c.sl R2N) c.n < c.C.n := fun h => by rw [h]; exact Nat.mod_lt _ (by omega)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  refine WP.block_append (WP.mono (checkRange_ok c hF.scr h0 (sl_le c h7 (i := K) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hf) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_)
  have hs₁ := hF.scr.of_rest k₁ (by decide)
  have v₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono (checkRange_ok c hs₁ h0 (sl_le c h7 (i := PT) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_rest k₂ (by decide)
  have K₂ := k₁.trans k₂
  have v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (v₁ hi hf)
  have U₂ : Unch base [(c.sl FLAG, 4)] s.mem s₂.mem := by
    have := O₁.unch.trans O₂.unch
    exact this.mono fun w hw => by simpa using hw
  have F₂ := F.unch h7 hn fixedOk_flag U₂
  have flag₂ : flagW c base s₂ =
      mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := F.mn
    have hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ := (v₁ (by decide) (by decide)).trans hF.pt
    have hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := (v₁ (by decide) (by decide)).trans F.mn
    rw [f₂, f₁, hF.flag, mask32_and, mask32_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono (mulN_ok hc hs₂ (hF.far.of_rest K₂) (modN_of hc F₂.mn) (o := SM') (a := PT) (b := R2N) (by decide) (by decide)
    (by decide) (hr2lt F₂.r2n) (by decide)) fun s₃ ⟨hs₃, M₃, g₃, U₃, v₃, lt₃, e₃⟩ => ?_
  have F₃ := F₂.unch h7 hn (fixedOk_slWk h7 (by decide)) U₃
  have sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from F₂.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) (powWkN hc) hc.fn hnR
    (bitsAt_lt hc (j := 2) (by decide)) hs₃ ((hF.far.of_rest K₂).of_rest g₃) M₃ lt₃
    F₃.onen (fun t ht => by
      show s₃.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch U₃ h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide)),
        tbl_unch U₂ h7 (j := 2) (by decide) ht (tbl_apart_flag h7 h0 2 t)]
      exact hF.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega) henc) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_)
  rw [powWxN_eq] at U₄
  have hs₄ := hs₃.of_rest K₄ (by decide)
  have hf₄ := ((hF.far.of_rest K₂).of_rest g₃).of_rest K₄
  have F₄ := F₃.unch h7 hn (fixedOk_slWk h7 (by decide)) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_slWk h7 hi hl)
  have w₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact v₄
  -- `u` and `v`.
  rw [uv_eq]
  refine WP.seq ?_
  refine WP.seq (WP.mono (mulN_ok hc hs₄ hf₄ (modN_of hc F₄.mn) (o := EM') (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₄.r2n) (by decide))
    fun s₅ ⟨hs₅, M₅, g₅, U₅, v₅, lt₅, e₅⟩ => ?_)
  have F₅ := F₄.unch h7 hn (fixedOk_slWk h7 (by decide)) U₅
  have hf₅ := hf₄.of_rest g₅
  refine WP.seq (WP.mono (mulN_ok hc hs₅ hf₅ M₅ (o := RM') (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₅.r2n) (by decide))
    fun s₆ ⟨hs₆, M₆, g₆, U₆, v₆, lt₆, e₆⟩ => ?_)
  have F₆ := F₅.unch h7 hn (fixedOk_slWk h7 (by decide)) U₆
  have hf₆ := hf₅.of_rest g₆
  have acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide) (by decide), v₅ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (mulN_ok hc hs₆ hf₆ M₆ (o := UM) (a := EM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄) (by decide))
    fun s₇ ⟨hs₇, M₇, g₇, U₇, v₇, lt₇, e₇⟩ => ?_)
  have F₇ := F₆.unch h7 hn (fixedOk_slWk h7 (by decide)) U₇
  have hf₇ := hf₆.of_rest g₇
  have acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by
    rw [v₇ (by decide) (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono (mulN_ok hc hs₇ hf₇ M₇ (o := VM) (a := RM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄) (by decide))
    fun s₈ ⟨hs₈, M₈, g₈, U₈, v₈, lt₈, e₈⟩ => ?_)
  have F₈ := F₇.unch h7 hn (fixedOk_slWk h7 (by decide)) U₈
  have hf₈ := hf₇.of_rest g₈
  refine WP.seq (WP.mono (mulN_ok hc hs₈ hf₈ M₈ (o := U) (a := UM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from F₈.one]; omega) (by decide))
    fun s₉ ⟨hs₉, M₉, g₉, U₉, v₉, lt₉, e₉⟩ => ?_)
  have F₉ := F₈.unch h7 hn (fixedOk_slWk h7 (by decide)) U₉
  have hf₉ := hf₈.of_rest g₉
  refine WP.mono (mulN_ok hc hs₉ hf₉ M₉ (o := V) (a := VM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from F₉.one]; omega) (by decide))
    fun s₁₀ ⟨hs₁₀, M₁₀, g₁₀, U₁₀, v₁₀, lt₁₀, e₁₀⟩ => h s₁₀ ?_
  have F₁₀ := F₉.unch h7 hn (fixedOk_slWk h7 (by decide)) U₁₀
  -- What changed: the flag and `midW`, and the accumulator.
  have hsub : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ midW) → ∀ w, w ∈ slW c l ∨ w ∈ [(c.wk, 64 * c.n)] →
      w ∈ slWk c midW := fun hl w hw => by
    rcases hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    · exact List.mem_append_right _ hw
  have U' : Unch base (slWk c midW) s₂.mem s₁₀.mem :=
    (U₃.trans (U₄.trans (U₅.trans (U₆.trans (U₇.trans (U₈.trans (U₉.trans U₁₀))))))).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
      all_goals exact hsub (by decide) w hw
  have UW : Unch base ([(c.sl FLAG, 4)] ++ slWk c midW) s.mem s₁₀.mem :=
    (U₂.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · exact List.mem_append_right _ hw
  have a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun hi hl hf =>
    sv_unch UW h7 hn hi (apart_append (apart_flag h0 hf) (apart_slWk h7 hi hl))
  -- The values.
  have d₄ : sv c base s₄ D = dig c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  have k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  have em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀) := by
    rw [v₆ (i := EM') (by decide) (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from F₄.r2n]), d₄]
  have rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from F₅.r2n]),
      v₅ (i := K) (by decide) (by decide) (by decide), k₄]
  have um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄]
  have vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide) (by decide), rm₆, acc₇, w₄]
  have Kw : Rest work s s₁₀ := (K₂.mono (by decide)).trans ((g₃.mono callClob_work).trans ((K₄.mono powClob_work).trans
    ((g₅.mono callClob_work).trans ((g₆.mono callClob_work).trans ((g₇.mono callClob_work).trans ((g₈.mono callClob_work).trans
    ((g₉.mono callClob_work).trans (g₁₀.mono callClob_work))))))))
  refine ⟨hs₁₀, hF.far.of_rest Kw, hF.rest.trans (Kw.mono (by simp)), F₁₀,
    by rw [a (i := RX) (by decide) (by decide) (by decide), hF.rx],
    by rw [a (i := RY) (by decide) (by decide) (by decide), hF.ry],
    by rw [a (i := RZ) (by decide) (by decide) (by decide), hF.rz], fun t ht => ?_, ?_,
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
      v₉ (i := VM) (by decide) (by decide) (by decide), vm₈], ?_⟩
  · rw [tbl_unch UW h7 (j := 1) (by decide) ht (apart_append (tbl_apart_flag h7 h0 1 t)
      (tbl_apart_slWk h7 (by decide)))]
    exact hF.t₁ t ht
  · rw [flagW, flag_unch U' h7 h0 hn (by decide), ← flagW]
    exact flag₂
  · exact whole_of hF.unch UW (le_append (flag_le h0 h7) (slWk_le h7 (by decide)))

end VG.Proof.Ecdsa.Verify.Arm
