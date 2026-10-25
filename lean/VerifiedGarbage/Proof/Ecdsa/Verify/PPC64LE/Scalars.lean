module

public import VerifiedGarbage.Proof.Ecdsa.Verify.PPC64LE.Front
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Middle
import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Flags
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Keep
import VerifiedGarbage.Proof.Weierstrass.PPC64LE.Pow
import VerifiedGarbage.Proof.Mont.PPC64LE.Row
public import VerifiedGarbage.Proof.Ecdsa.PPC64LE.Stages

/-!
# ECDSA verification on PPC64LE: `u` and `v`

As on 32-bit ARM (`Proof/Ecdsa/Verify/Arm/Scalars.lean`). `mid_ok`: the
masks of `r` and `s` in `[1, n-1]` into the flag, `w = s^(n-2)` in
Montgomery form modulo `n`, and `u = e w` and `v = r w`, out of it.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.PPC64LE

open VG VG.PPC64LE VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.PPC64LE
open VG.Impl.Weierstrass.PPC64LE.Mont VG.Impl.Ecdsa.PPC64LE
open VG.Proof.Mont VG.Proof.Mont.PPC64LE VG.Proof.Weierstrass VG.Proof.Weierstrass.PPC64LE
  VG.Proof.Weierstrass.PPC64LE.Mont VG.Proof.Ecdsa.PPC64LE VG.Proof.Ecdh.PPC64LE VG.Spec.Weierstrass
open VG.Impl.Ecdh.PPC64LE (PX PY)
open VG.Impl.Ecdsa.Verify.PPC64LE (SM' EM' RM' UM VM U V)

variable {c : Cfg}

/-- The slots `mid_ok` writes. -/
abbrev midW : List Nat := [SM', ACC, PT, EM', RM', UM, VM, U, V]

/-- After `u` and `v`. -/
structure Mid (c : Cfg) (s₀ : State) (base : Addr) (s : State) : Prop extends Keep c s₀ base s where
  rx : sv c base s RX = 0
  ry : sv c base s RY = c.mont 1
  rz : sv c base s RZ = 0
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
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

theorem scalars_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c =
    .seq (.block (c.checkRange (c.sl K) ++ c.checkRange (c.sl PT)))
      (mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N)) := rfl

theorem uv_eq (c : Cfg) : Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c =
    .seq (mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N))
    (.seq (mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC))
    (.seq (mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC))
    (.seq (mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE))
      (mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE)))))) := rfl

/-- One multiplication modulo `n` from what the stages keep. -/
theorem mulN_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State} (K₀ : Keep c s₀ base s)
    {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45) (hoF : o = TMP ∨ 12 ≤ o) (hof : FLAG ≠ o)
    (hB : sv c base s b < c.C.n) :
    WP isa (mulCall c.SN (c.sl o) (c.sl a) (c.sl b)) s fun s' =>
      Keep c s₀ base s' ∧ flagW c base s' = flagW c base s ∧
      (∀ {j}, j < 3 → ∀ t < 64 * c.n,
        s'.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t))) ∧
      (∀ {i}, i < 45 → i ≠ o → sv c base s' i = sv c base s i) ∧
      sv c base s' o < c.C.n ∧
      sv c base s' o * 2 ^ (64 * c.n) % c.C.n = sv c base s a * sv c base s b % c.C.n :=
  WP.mono (slMul_ok hc.fn hc.fnk hc.fnm hc.n10 K₀.ws ho ha hb hB) fun _ ⟨k, U, lt, e⟩ =>
    have := K₀.call hc.n0 hc.n10 ho hoF hof k U
    ⟨this.1, this.2.1, this.2.2.1, this.2.2.2, lt, e⟩

/-- The checks of `r` and `s`, `w = s^(n-2)`, `u` and `v`. -/
theorem mid_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hF : Front c s₀ base s) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Mid c s₀ base s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.scalars c) (.seq (pow c.powN c.SN)
      (.seq (Impl.Ecdsa.Verify.PPC64LE.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.ws.nowrap
  have hsz : size = 8192 := rfl
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have hfl : c.sl FLAG + 8 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  have hl : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => by have := sl_le c h7 hi; omega_arith
  have hr2lt : 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n < c.C.n := Nat.mod_lt _ (by omega_arith)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  refine wp_append (WP.mono (checkRange_ok c hF.ws.ws hF.ws.at3 (sl_al c K) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₁ ⟨f₁, k₁, O₁⟩ => ?_)
  have K₁ := hF.toKeep.step h7 (k₁.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₁.unch)
    (hW := fixedOk_flag) (hWs := flag_le h7)
  refine WP.mono (checkRange_ok c K₁.ws.ws K₁.ws.at3 (sl_al c PT) h0 (hl (by decide)) (hl (by decide)) hfl)
    fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  have K₂ := K₁.step h7 (k₂.rk (rs' := [.r0, .r4, .r5, .r6, .r7, .r8, .r9])) (hU := O₂.unch)
    (hW := fixedOk_flag) (hWs := flag_le h7)
  have v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_unch O₂.unch h7 hn hi (apart_flag h0 hf)).trans (sv_unch O₁.unch h7 hn hi (apart_flag h0 hf))
  have t₂ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₂.mem (off base (bitsAt c.n j + t)) = s.mem (off base (bitsAt c.n j + t)) := fun hj t ht => by
    rw [tbl_unch O₂.unch h7 hj ht (tbl_apart_flag h7 h0 _ t), tbl_unch O₁.unch h7 hj ht (tbl_apart_flag h7 h0 _ t)]
  have flag₂ : flagW c base s₂ =
      mask64 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := hF.fixed.mn
    have hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ :=
      (sv_unch O₁.unch h7 hn (i := PT) (by decide) (apart_flag h0 (by decide))).trans hF.pt
    have hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := K₁.fixed.mn
    rw [f₂, f₁, hF.flag, mask64_and, mask64_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono (mulN_ok hc K₂ (o := SM') (a := PT) (b := R2N) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [show sv c base s₂ R2N = _ from K₂.fixed.r2n]; exact hr2lt))
    fun s₃ ⟨K₃, f₃, t₃, v₃, lt₃, e₃⟩ => ?_
  have sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from K₂.fixed.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (S := c.SN) (e := c.C.n - 2) hc.fnk hc.fnm (modN hc) rfl
    (powLayN hc) hnR K₃.ws (show sv c base s₃ KM < c.C.n from lt₃) K₃.fixed.onen
    (fun t ht => by
      show s₃.mem (off base (bitsAt c.n 2 + t)) = _
      rw [t₃ (j := 2) (by decide) t ht, t₂ (j := 2) (by decide) t ht]
      exact hF.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith)) fun s₄ ⟨k₄, U₄, lt₄, w₄⟩ => ?_)
  rw [powWxN_eq] at U₄
  have K₄ := K₃.step h7 k₄ (hU := U₄) (hW := fixedOk_powWx h7) (hWs := powWx_le h7)
  have e₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_powWx h7 hi hl)
  have f₄ : flagW c base s₄ = flagW c base s₃ := by
    simp only [flagW]
    exact U₄.word (fun w hw => by
      rcases apart_powWx h7 (i := FLAG) (by decide) (by decide) w hw with h | h
      · exact Or.inl (by omega_arith)
      · exact Or.inr h) (by have := sl_le c h7 (i := FLAG) (by decide); omega_arith)
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off base (bitsAt c.n j + t)) = s₃.mem (off base (bitsAt c.n j + t)) := fun hj t ht =>
    tbl_unch U₄ h7 hj ht (tbl_apart_powWx h7 _ t)
  have w₄' : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact w₄
  -- `u` and `v`.
  rw [uv_eq]
  refine WP.seq ?_
  refine WP.seq (WP.mono (mulN_ok hc K₄ (o := EM') (a := D) (b := R2N) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₄ R2N = _ from K₄.fixed.r2n]; exact hr2lt))
    fun s₅ ⟨K₅, f₅, t₅, v₅, lt₅, e₅⟩ => ?_)
  refine WP.seq (WP.mono (mulN_ok hc K₅ (o := RM') (a := K) (b := R2N) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₅ R2N = _ from K₅.fixed.r2n]; exact hr2lt))
    fun s₆ ⟨K₆, f₆, t₆, v₆, lt₆, e₆⟩ => ?_)
  have acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide), v₅ (by decide) (by decide)]
  refine WP.seq (WP.mono (mulN_ok hc K₆ (o := UM) (a := EM') (b := ACC) (by decide) (by decide) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄)) fun s₇ ⟨K₇, f₇, t₇, v₇, lt₇, e₇⟩ => ?_)
  have acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by rw [v₇ (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono (mulN_ok hc K₇ (o := VM) (a := RM') (b := ACC) (by decide) (by decide) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄)) fun s₈ ⟨K₈, f₈, t₈, v₈, lt₈, e₈⟩ => ?_)
  refine WP.seq (WP.mono (mulN_ok hc K₈ (o := U) (a := UM) (b := ONE) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from K₈.fixed.one]; omega_arith))
    fun s₉ ⟨K₉, f₉, t₉, v₉, lt₉, e₉⟩ => ?_)
  refine WP.mono (mulN_ok hc K₉ (o := V) (a := VM) (b := ONE) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from K₉.fixed.one]; omega_arith))
    fun s₁₀ ⟨K₁₀, f₁₀, t₁₀, v₁₀, lt₁₀, e₁₀⟩ => h s₁₀ ?_
  -- What reaches `s₁₀` from `s`.
  have a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun hi hl hf => by
    simp only [midW, List.mem_cons, List.not_mem_nil, or_false, not_or] at hl
    obtain ⟨h1, h2, h3, h4, h5, h6, h7', h8, h9⟩ := hl
    rw [v₁₀ hi h9, v₉ hi h8, v₈ hi h7', v₇ hi h6, v₆ hi h5, v₅ hi h4, e₄ hi (by simp [h2, h3]), v₃ hi h1,
      v₂ hi hf]
  -- The values.
  have d₄ : sv c base s₄ D = dig c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  have k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  have em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀) := by
    rw [v₆ (i := EM') (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from K₄.fixed.r2n]), d₄]
  have rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from K₅.fixed.r2n]),
      v₅ (i := K) (by decide) (by decide), k₄]
  have um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄']
  have vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide), rm₆, acc₇, w₄']
  refine ⟨K₁₀,
    by rw [a (i := RX) (by decide) (by decide) (by decide), hF.rx],
    by rw [a (i := RY) (by decide) (by decide) (by decide), hF.ry],
    by rw [a (i := RZ) (by decide) (by decide) (by decide), hF.rz], fun t ht => ?_,
    by rw [f₁₀, f₉, f₈, f₇, f₆, f₅, f₄, f₃, flag₂],
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px_lt,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py_lt,
    by rw [a (i := PX) (by decide) (by decide) (by decide)]; exact hF.px,
    by rw [a (i := PY) (by decide) (by decide) (by decide)]; exact hF.py,
    by rw [v₁₀ (by decide) (by decide), v₉ (by decide) (by decide), v₈ (by decide) (by decide),
      v₇ (by decide) (by decide)]; exact lt₆,
    by rw [v₁₀ (by decide) (by decide), v₉ (by decide) (by decide), v₈ (by decide) (by decide),
      v₇ (by decide) (by decide), rm₆],
    by rw [v₁₀ (by decide) (by decide)]; exact lt₉,
    by rw [v₁₀ (i := U) (by decide) (by decide),
      toM_one_mul hnR (by rw [e₉, show sv c base s₈ ONE = 1 from K₈.fixed.one]), um₈],
    lt₁₀,
    by rw [toM_one_mul hnR (by rw [e₁₀, show sv c base s₉ ONE = 1 from K₉.fixed.one]),
      v₉ (i := VM) (by decide) (by decide), vm₈]⟩
  rw [t₁₀ (j := 1) (by decide) t ht, t₉ (j := 1) (by decide) t ht, t₈ (j := 1) (by decide) t ht,
    t₇ (j := 1) (by decide) t ht, t₆ (j := 1) (by decide) t ht, t₅ (j := 1) (by decide) t ht,
    t₄ (j := 1) (by decide) t ht, t₃ (j := 1) (by decide) t ht, t₂ (j := 1) (by decide) t ht]
  exact hF.t₁ t ht

end VG.Proof.Ecdsa.Verify.PPC64LE
