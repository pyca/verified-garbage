module

import VerifiedGarbage.Proof.Framework.Arm.Syms
import VerifiedGarbage.Proof.Ecdh.Arm.Peer
import VerifiedGarbage.Proof.Ecdsa.Arm.Lays
import VerifiedGarbage.Proof.Ecdsa.Arm.SlotOps
import VerifiedGarbage.Proof.Weierstrass.Arm.Copy
import VerifiedGarbage.Proof.Weierstrass.Arm.Saves
import VerifiedGarbage.Proof.Weierstrass.Arm.Const
import VerifiedGarbage.Proof.Ecdsa.Arm.Finish
import VerifiedGarbage.Proof.Ecdsa.Arm.Scalar
import VerifiedGarbage.Proof.Ecdsa.Arm.Middle
import VerifiedGarbage.Proof.Ecdsa.Arm.Setup
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.X25519.Arm.Limbs
public import VerifiedGarbage.Proof.Ecdsa.Arm.Main
public import VerifiedGarbage.Proof.Weierstrass.Arm.LadderP
public import VerifiedGarbage.Proof.Weierstrass.Arm.Ladder
public import VerifiedGarbage.Proof.Ecdsa.Verify.Arm.Front

/-! ### `Ecdsa.Verify.Arm.Scalars`, which this module and modules that import it used -/

section

/-!
# ECDSA verification on 32-bit ARM: `u` and `v`

As on x86 (`Proof/Ecdsa/Verify/X86/Points.lean`).

`mid_ok`: from what `front_ok` leaves, `scalars` ands the masks of `r` and
`s` in `[1, n-1]` into the flag and computes `s R mod n`, the signature's
power modulo `n` gives `w = s^(n-2)` (in Montgomery form), and `uv` computes
`r R mod n` (`RM'`) and `u = e w` and `v = r w` modulo `n`, out of
Montgomery's form (`U`, `V`), with the multiplications of `Proof/Mont`.
-/

@[expose] public section

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
      (Mont.mulCall c.SN (c.sl SM') (c.sl PT) (c.sl R2N) c.umaal) := rfl

theorem uv_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.uv c =
    .seq (Mont.mulCall c.SN (c.sl EM') (c.sl D) (c.sl R2N) c.umaal)
    (.seq (Mont.mulCall c.SN (c.sl RM') (c.sl K) (c.sl R2N) c.umaal)
    (.seq (Mont.mulCall c.SN (c.sl UM) (c.sl EM') (c.sl ACC) c.umaal)
    (.seq (Mont.mulCall c.SN (c.sl VM) (c.sl RM') (c.sl ACC) c.umaal)
    (.seq (Mont.mulCall c.SN (c.sl U) (c.sl UM) (c.sl ONE) c.umaal)
      (Mont.mulCall c.SN (c.sl V) (c.sl VM) (c.sl ONE) c.umaal))))) := rfl

/-- One multiplication modulo `n`, on numbered slots: it keeps the modulus and
every other slot but the temporary area's. -/
theorem mulN_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (hf : Far s base 8192)
    (hMN : ModOkW c.MN' size c.C.n s.mem base) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hB : sv c base s b < c.C.n) (hoN : o ≠ MN) :
    WP isa (Mont.mulCall c.SN (c.sl o) (c.sl a) (c.sl b) c.umaal) s fun s' =>
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
    WP isa (.seq (Impl.Ecdsa.Verify.Arm.Cfg.scalars c) (.seq (pow c.powN c.SN c.umaal)
      (.seq (Impl.Ecdsa.Verify.Arm.Cfg.uv c) rest))) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hF.scr.nowrap
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hn3 := hc.n_ge
  have F := hF.fixed
  obtain hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_arith
  obtain henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  obtain hr2lt : ∀ {m : Mem}, wordsVal m base (c.sl R2N) c.n = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n →
      wordsVal m base (c.sl R2N) c.n < c.C.n := fun h => by rw [h]; exact Nat.mod_lt _ (by omega_arith)
  rw [scalars_eq]
  -- The checks.
  refine WP.seq (WP.seq ?_)
  refine WP.block_append (WP.mono (checkRange_ok c hF.scr h0 (sl_le c h7 (i := K) (by decide))
    (sl_le c h7 (i := MN) (by decide)) hf) fun s₁ ⟨f₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hF.scr.of_rest k₁ (by decide)
  obtain v₁ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₁ i = sv c base s i := fun hi hf =>
    sv_flag O₁ h0 h7 hn hi hf
  refine WP.mono (checkRange_ok c hs₁ h0 (sl_le c h7 (i := PT) (by decide)) (sl_le c h7 (i := MN) (by decide))
    hf) fun s₂ ⟨f₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  obtain K₂ := k₁.trans k₂
  obtain v₂ : ∀ {i}, i < 45 → i ≠ FLAG → sv c base s₂ i = sv c base s i := fun hi hf =>
    (sv_flag O₂ h0 h7 hn hi hf).trans (v₁ hi hf)
  obtain U₂ : Unch base [(c.sl FLAG, 4)] s.mem s₂.mem := by
    have := O₁.unch.trans O₂.unch
    exact this.mono fun w hw => by simpa using hw
  obtain F₂ := F.unch h7 hn fixedOk_flag U₂
  obtain flag₂ : flagW c base s₂ =
      mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) := by
    have hk : wordsVal s.mem base (c.sl K) c.n = sigR c s₀ := hF.k
    have hmn : wordsVal s.mem base (c.sl MN) c.n = c.C.n := F.mn
    obtain hpt₁ : wordsVal s₁.mem base (c.sl PT) c.n = sigS c s₀ := (v₁ (by decide) (by decide)).trans hF.pt
    obtain hmn₁ : wordsVal s₁.mem base (c.sl MN) c.n = c.C.n := (v₁ (by decide) (by decide)).trans F.mn
    rw [f₂, f₁, hF.flag, mask32_and, mask32_and, hmn₁, hmn, hk, hpt₁]
    simp only [and_assoc]
  -- `s R mod n`.
  refine WP.mono (mulN_ok hc hs₂ (hF.far.of_rest K₂) (modN_of hc F₂.mn) (o := SM') (a := PT) (b := R2N) (by decide) (by decide)
    (by decide) (hr2lt F₂.r2n) (by decide)) fun s₃ ⟨hs₃, M₃, g₃, U₃, v₃, lt₃, e₃⟩ => ?_
  obtain F₃ := F₂.unch h7 hn (fixedOk_slWk h7 (by decide)) U₃
  obtain sm₃ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₃ SM') = Fin.ofNat c.C.n (sigS c s₀) := by
    rw [toM_r2 hnR (by rw [e₃, show sv c base s₂ R2N = _ from F₂.r2n]), v₂ (by decide) (by decide), hF.pt]
  -- `w = s^(n-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) (powWkN hc) hc.fn hnR
    (bitsAt_lt hc (j := 2) (by decide)) hs₃ ((hF.far.of_rest K₂).of_rest g₃) M₃ lt₃
    F₃.onen (fun t ht => by
      show s₃.mem (off base (bitsAt c.n 2 + t)) = _
      rw [tbl_unch U₃ h7 (j := 2) (by decide) ht (tbl_apart_slWk h7 (by decide)),
        tbl_unch U₂ h7 (j := 2) (by decide) ht (tbl_apart_flag h7 h0 2 t)]
      exact hF.t₂ t ht)
    (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega_arith) henc) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => ?_)
  rw [powWxN_eq] at U₄
  obtain hs₄ := hs₃.of_rest K₄ (by decide)
  obtain hf₄ := ((hF.far.of_rest K₂).of_rest g₃).of_rest K₄
  obtain F₄ := F₃.unch h7 hn (fixedOk_slWk h7 (by decide)) U₄
  obtain e₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi hl =>
    sv_unch U₄ h7 hn hi (apart_slWk h7 hi hl)
  obtain w₄ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₄ ACC) = Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [← sm₃]; exact v₄
  -- `u` and `v`.
  rw [uv_eq]
  refine WP.seq ?_
  refine WP.seq (WP.mono (mulN_ok hc hs₄ hf₄ (modN_of hc F₄.mn) (o := EM') (a := D) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₄.r2n) (by decide))
    fun s₅ ⟨hs₅, M₅, g₅, U₅, v₅, lt₅, e₅⟩ => ?_)
  obtain F₅ := F₄.unch h7 hn (fixedOk_slWk h7 (by decide)) U₅
  obtain hf₅ := hf₄.of_rest g₅
  refine WP.seq (WP.mono (mulN_ok hc hs₅ hf₅ M₅ (o := RM') (a := K) (b := R2N) (by decide)
    (by decide) (by decide) (hr2lt F₅.r2n) (by decide))
    fun s₆ ⟨hs₆, M₆, g₆, U₆, v₆, lt₆, e₆⟩ => ?_)
  obtain F₆ := F₅.unch h7 hn (fixedOk_slWk h7 (by decide)) U₆
  obtain hf₆ := hf₅.of_rest g₆
  obtain acc₆ : sv c base s₆ ACC = sv c base s₄ ACC := by
    rw [v₆ (by decide) (by decide) (by decide), v₅ (by decide) (by decide) (by decide)]
  refine WP.seq (WP.mono (mulN_ok hc hs₆ hf₆ M₆ (o := UM) (a := EM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₆ ▸ lt₄) (by decide))
    fun s₇ ⟨hs₇, M₇, g₇, U₇, v₇, lt₇, e₇⟩ => ?_)
  obtain F₇ := F₆.unch h7 hn (fixedOk_slWk h7 (by decide)) U₇
  obtain hf₇ := hf₆.of_rest g₇
  obtain acc₇ : sv c base s₇ ACC = sv c base s₄ ACC := by
    rw [v₇ (by decide) (by decide) (by decide), acc₆]
  refine WP.seq (WP.mono (mulN_ok hc hs₇ hf₇ M₇ (o := VM) (a := RM') (b := ACC) (by decide)
    (by decide) (by decide) (acc₇ ▸ lt₄) (by decide))
    fun s₈ ⟨hs₈, M₈, g₈, U₈, v₈, lt₈, e₈⟩ => ?_)
  obtain F₈ := F₇.unch h7 hn (fixedOk_slWk h7 (by decide)) U₈
  obtain hf₈ := hf₇.of_rest g₈
  refine WP.seq (WP.mono (mulN_ok hc hs₈ hf₈ M₈ (o := U) (a := UM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₈ ONE = 1 from F₈.one]; omega_arith) (by decide))
    fun s₉ ⟨hs₉, M₉, g₉, U₉, v₉, lt₉, e₉⟩ => ?_)
  obtain F₉ := F₈.unch h7 hn (fixedOk_slWk h7 (by decide)) U₉
  obtain hf₉ := hf₈.of_rest g₉
  refine WP.mono (mulN_ok hc hs₉ hf₉ M₉ (o := V) (a := VM) (b := ONE) (by decide)
    (by decide) (by decide) (by rw [show sv c base s₉ ONE = 1 from F₉.one]; omega_arith) (by decide))
    fun s₁₀ ⟨hs₁₀, M₁₀, g₁₀, U₁₀, v₁₀, lt₁₀, e₁₀⟩ => h s₁₀ ?_
  obtain F₁₀ := F₉.unch h7 hn (fixedOk_slWk h7 (by decide)) U₁₀
  -- What changed: the flag and `midW`, and the accumulator.
  obtain hsub : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ midW) → ∀ w, w ∈ slW c l ∨ w ∈ [(c.wk, 64 * c.n)] →
      w ∈ slWk c midW := fun hl w hw => by
    rcases hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    · exact List.mem_append_right _ hw
  obtain U' : Unch base (slWk c midW) s₂.mem s₁₀.mem :=
    (U₃.trans (U₄.trans (U₅.trans (U₆.trans (U₇.trans (U₈.trans (U₉.trans U₁₀))))))).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw | hw | hw | hw
      all_goals exact hsub (by decide) w hw
  obtain UW : Unch base ([(c.sl FLAG, 4)] ++ slWk c midW) s.mem s₁₀.mem :=
    (U₂.trans U').mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · exact List.mem_append_right _ hw
  obtain a : ∀ {i}, i < 45 → i ∉ midW → i ≠ FLAG → sv c base s₁₀ i = sv c base s i := fun hi hl hf =>
    sv_unch UW h7 hn hi (apart_append (apart_flag h0 hf) (apart_slWk h7 hi hl))
  -- The values.
  obtain d₄ : sv c base s₄ D = dig c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.d]
  obtain k₄ : sv c base s₄ K = sigR c s₀ := by
    rw [e₄ (by decide) (by decide), v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide), hF.k]
  obtain em₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ EM') = Fin.ofNat c.C.n (dig c s₀) := by
    rw [v₆ (i := EM') (by decide) (by decide) (by decide),
      toM_r2 hnR (by rw [e₅, show sv c base s₄ R2N = _ from F₄.r2n]), d₄]
  obtain rm₆ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₆ RM') = Fin.ofNat c.C.n (sigR c s₀) := by
    rw [toM_r2 hnR (by rw [e₆, show sv c base s₅ R2N = _ from F₅.r2n]),
      v₅ (i := K) (by decide) (by decide) (by decide), k₄]
  obtain um₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ UM) =
      Fin.ofNat c.C.n (dig c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [v₈ (i := UM) (by decide) (by decide) (by decide), toM_mul hnR e₇, em₆, acc₆, w₄]
  obtain vm₈ : toM c.C.n (2 ^ (64 * c.n)) (sv c base s₈ VM) =
      Fin.ofNat c.C.n (sigR c s₀) * Fin.ofNat c.C.n (sigS c s₀) ^ (c.C.n - 2) := by
    rw [toM_mul hnR e₈, v₇ (i := RM') (by decide) (by decide) (by decide), rm₆, acc₇, w₄]
  obtain Kw : Rest work s s₁₀ := (K₂.mono (by decide)).trans ((g₃.mono callClob_work).trans ((K₄.mono powClob_work).trans
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

end

end

/-! ### `Ecdsa.Verify.Arm.Generator`, which this module and modules that import it used -/

section

/-! The verification pipeline can use any verified fixed-base multiplication. -/

@[expose] public section
namespace VG.Proof.Ecdsa.Verify.Arm
open VG VG.Arm VG.Impl.Ecdsa.Arm VG.Impl.Weierstrass.Arm
open VG.Proof.Mont VG.Proof.Mont.Arm VG.Proof.Weierstrass VG.Proof.Weierstrass.Arm
open VG.Proof.Ecdsa.Arm VG.Proof.X25519.Arm
open Spec.Weierstrass

def GeneratorWP (c : Cfg) (generator : Prog isa) (s₀ : State) (base : Addr) (k : Nat)
    (Q : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (symbols : String → BitVec 32) (a0 : Bool := false) : Prop :=
  ∀ s, Scr s base size → Far s base 8192 → Fixed c base s₀.gpr s.mem →
    (∀ x ∈ ladR c.ladderCfg,wordsVal s.mem base x c.MP'.n<c.C.p) →
    Step c.ladderCfg c.C base s k Q a0 →
    Q c.ladderCfg.nbits (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY))
      (tmv c.C c.n base s (c.sl RZ)) →
    sv c base s RX = 0 → sv c base s RY = c.mont 1 → sv c base s RZ = 0 →
    (c.mul = none → ∀ i<64*c.n,s.mem (off base (bitsAt c.n 0+i))=if k.testBit i then 1 else 0) →
    (c.mul.isSome → sv c base s K = k) →
    Rest (.lr::work) s₀ s → Unch base [(0,8192)] s₀.mem s.mem → s.syms=symbols →
    WP isa generator s fun t =>
      Rest powClob s t ∧ Unch base (Point.ladWp c.ladderCfg c.wk ++ genX c) s.mem t.mem ∧
      ModOkW c.MP' size c.C.p t.mem base ∧
      (∀ x∈[c.sl RX,c.sl RY,c.sl RZ],wordsVal t.mem base x c.n<c.C.p) ∧
      Q 0 (tmv c.C c.n base t (c.sl RX)) (tmv c.C c.n base t (c.sl RY)) (tmv c.C c.n base t (c.sl RZ))

/-- `gen`: the call or the ladder, for the invariant that `R` represents
`[k >>> j]G`. -/
theorem generatorWP_gen {c : Cfg} (hc : CfgOk c) (hC : Law c.C) {s₀ : State} {base : Addr} {k : Nat}
    {symbols : String → BitVec 32} (hkl : k < 2 ^ (8 * c.C.len)) :
    GeneratorWP c c.gen s₀ base k (fun j X Y Z => Rep c.C X Y Z (mul (k >>> j) (G c.C))) symbols c.qA0 := by
  intro s hs hf F _ _ _ hrx hry hrz bits hk _ _ _
  have hp := hc.p_ge
  refine WP.mono (qMul_ok hc hC hs hf F (px := GX) (py := GY) (by decide)
    (lt_of_eq_of_lt F.gx (Nat.mod_lt _ (by omega_using [hp])))
    (lt_of_eq_of_lt F.gy (Nat.mod_lt _ (by omega_using [hp]))) hrx hry hrz hc.onG (by
      show Rep c.C (toM _ _ (wordsVal s.mem base (c.sl GX) c.n)) (toM _ _ (wordsVal s.mem base (c.sl GY) c.n))
        1 (G c.C)
      rw [F.gx, F.gy, toM_cmont hc, toM_cmont hc]
      exact rep_affine' hC _ _) hkl hk bits) fun t ⟨K, U, M, L, R⟩ =>
    ⟨K, U, M, L, by simpa only [Nat.shiftRight_zero] using R⟩

end VG.Proof.Ecdsa.Verify.Arm

end

end

/-! ### `Ecdsa.Verify.Arm.Points`, which only this module used -/

section

/-!
# ECDSA verification on 32-bit ARM: `[u]G + [v]Q`

As on x86 (`Proof/Ecdsa/Verify/X86/Points.lean`).

`pointsWith_ok`: from what `mid_ok` leaves, the table of `u`'s bits, the
signature's ladder (from `G`), `save` (`[u]G` to `U`, and `R = O`), the
table of `v`'s bits, ECDH's ladder (from the key's point) and `sum` (the
complete addition of `U` and `R`, into `R`), for any invariants of the two
ladders: `R` holds `rcbAdd` of what the two ladders end with. `Main.lean`
gives the invariants of the group law.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest)
open VG.Impl.Ecdh.Arm (PX PY)
open VG.Impl.Ecdsa.Verify.Arm (SM' EM' RM' UM VM U V UX UY UZ)

variable {c : Cfg}

theorem tbl_le (h7 : c.n < 10) : bitsAt c.n 0 + 64 * c.n ≤ 8192 := bitsAt_le c h7 (j := 0) (by decide)

/-- `[o] = x`, on numbered slots. -/
theorem setSl_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) {o x : Nat}
    (ho : o < 45) (hx : x < 2 ^ (64 * c.n)) :
    WP isa (.block (setConst c.n (c.sl o) x)) s fun s' =>
      sv c base s' o = x ∧ Rest [.r4] s s' ∧ Outside base (c.sl o) (8 * c.n) s.mem s'.mem :=
  setConst_ok hs (sl_le c hc.n10 ho) hx

/-- The slots `save` writes. -/
abbrev saveW : List Nat := [UX, UY, UZ, RX, RY, RZ]

theorem save_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.save c =
    copy (2 * c.n) (c.sl UX) (c.sl RX) ++ (copy (2 * c.n) (c.sl UY) (c.sl RY) ++
    (copy (2 * c.n) (c.sl UZ) (c.sl RZ) ++ (setConst c.n (c.sl RX) 0 ++
    (setConst c.n (c.sl RY) (c.mont 1) ++ setConst c.n (c.sl RZ) 0)))) := by
  simp only [Impl.Ecdsa.Verify.Arm.Cfg.save, List.append_assoc]

/-- `U = R`, and `R = O`. -/
theorem save_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) :
    WP isa (.block (Impl.Ecdsa.Verify.Arm.Cfg.save c)) s fun s' =>
      Scr s' base size ∧ Rest [.r4] s s' ∧ Unch base (slW c saveW) s.mem s'.mem ∧
      sv c base s' UX = sv c base s RX ∧ sv c base s' UY = sv c base s RY ∧
      sv c base s' UZ = sv c base s RZ ∧ sv c base s' RX = 0 ∧ sv c base s' RY = c.mont 1 ∧
      sv c base s' RZ = 0 := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hp := hc.p_lt
  have hp3 := hc.p_ge
  obtain hm1 : c.mont 1 < 2 ^ (64 * c.n) := by
    have : c.mont 1 < c.C.p := Nat.mod_lt _ (by omega_using [hp3])
    omega_using [hp, this]
  rw [save_eq]
  refine WP.block_append (WP.mono (copySl_ok hc hs (o := UX) (a := RX) (by decide) (by decide) (by decide))
    fun s₁ ⟨e₁, k₁, O₁⟩ => ?_)
  obtain hs₁ := hs.of_rest k₁ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := UY) (a := RY) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := UZ) (a := RZ) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₃ (o := RX) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_)
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  refine WP.block_append (WP.mono (setSl_ok hc hs₄ (o := RY) (by decide) hm1) fun s₅ ⟨e₅, k₅, O₅⟩ => ?_)
  obtain hs₅ := hs₄.of_rest k₅ (by decide)
  refine WP.mono (setSl_ok hc hs₅ (o := RZ) (x := 0) (by decide) (Nat.two_pow_pos _))
    fun s₆ ⟨e₆, k₆, O₆⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  refine ⟨hs₅.of_rest k₆ (by decide), k₁.trans (k₂.trans (k₃.trans (k₄.trans (k₅.trans k₆)))), ?_,
    ?_, ?_, ?_, ?_, ?_, e₆⟩
  · have := O₁.unch.trans (O₂.unch.trans (O₃.unch.trans (O₄.unch.trans (O₅.unch.trans O₆.unch))))
    exact this.mono fun w hw => by simpa [saveW] using hw
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), o O₂ (by decide) (by decide), e₁]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide),
      o O₃ (by decide) (by decide), e₂, o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), o O₄ (by decide) (by decide), e₃,
      o O₂ (by decide) (by decide), o O₁ (by decide) (by decide)]
  · rw [o O₆ (by decide) (by decide), o O₅ (by decide) (by decide), e₄]
  · rw [o O₆ (by decide) (by decide), e₅]

/-- The slots `sum` writes. -/
abbrev sumW : List Nat := [T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP, RX, RY, RZ]

/-- The slots of the addition. -/
abbrev sumSl : List Nat := [AP, B3P, T0, T1, T2, T3, T4, T5, DX, DY, DZ, UX, UY, UZ, RX, RY, RZ]

/-- The slots it reads. -/
abbrev sumR : List Nat := [AP, B3P, UX, UY, UZ, RX, RY, RZ]

theorem sum_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.sum c =
    .seq (fprog c.SP (rcb c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ)) c.umaal)
      (.block (copy (2 * c.n) (c.sl RX) (c.sl DX) ++ (copy (2 * c.n) (c.sl RY) (c.sl DY) ++
        copy (2 * c.n) (c.sl RZ) (c.sl DZ)))) := by
  simp only [Impl.Ecdsa.Verify.Arm.Cfg.sum, List.append_assoc]

/-- `R = U + R`, by the complete addition. -/
theorem sum_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hlt : ∀ i ∈ sumR, sv c base s i < c.C.p) :
    WP isa (Impl.Ecdsa.Verify.Arm.Cfg.sum c) s fun s' =>
      Scr s' base size ∧ Rest Mont.callClob s s' ∧ Unch base (slWk c sumW) s.mem s'.mem ∧
      ModOkW c.MP' size c.C.p s'.mem base ∧ sv c base s' RZ < c.C.p ∧
      (tmv c.C c.n base s' (c.sl RX), tmv c.C c.n base s' (c.sl RY), tmv c.C c.n base s' (c.sl RZ)) =
        rcbAdd (tmv c.C c.n base s (c.sl AP)) (tmv c.C c.n base s (c.sl B3P))
          (tmv c.C c.n base s (c.sl UX)) (tmv c.C c.n base s (c.sl UY)) (tmv c.C c.n base s (c.sl UZ))
          (tmv c.C c.n base s (c.sl RX)) (tmv c.C c.n base s (c.sl RY)) (tmv c.C c.n base s (c.sl RZ)) := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hL : Lay c.MP' size (· ∈ sumSl.map c.sl) := lay_map hc rfl rfl rfl (by decide)
  obtain hW : WkOk c.MP' size c.wk (· ∈ sumSl.map c.sl) := ⟨wk_le c h7 rfl, fun x hx => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have : ∀ i ∈ sumSl, i < 45 := by decide
      exact sl_below_wk c hc.n10 (this i hi),
    sl_below_wk c hc.n10 (i := MP) (by decide), sl_below_wk c hc.n10 (i := TMP) (by decide)⟩
  obtain hA : RcbApart c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) (c.pt DX DY DZ) :=
    rcbApart_of h0 (lw := [T0, T1, T2, T3, T4, T5, DX, DY, DZ]) (lr := sumR) rfl rfl (by decide)
      (by decide)
  obtain hI : Inv c.MP' base size c.C.p (· ∈ sumSl.map c.sl) (sumR.map c.sl)
      (fun x => toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base x c.n)) s := by
    refine ⟨hs, hM, fun x hx => ?_, fun x hx => ?_, fun _ _ => rfl, hf⟩
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      obtain sub : ∀ i ∈ sumR, i ∈ sumSl := by decide
      exact List.mem_map_of_mem (sub i hi)
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      exact hlt i hi
  rw [sum_eq]
  refine WP.seq (WP.mono (rcb_ok hL hW hc.fp hpR hA (fun x hx => ?_) hI (fun x hx => hx))
    fun s₁ ⟨PK, I₁, t₁, _⟩ => ?_)
  · rw [show rcbW c.rcbSlots (c.pt DX DY DZ) ++ rcbR c.rcbSlots (c.pt UX UY UZ) (c.pt RX RY RZ) =
      ([T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR).map c.sl from rfl] at hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain sub : ∀ i ∈ [T0, T1, T2, T3, T4, T5, DX, DY, DZ] ++ sumR, i ∈ sumSl := by decide
    exact List.mem_map_of_mem (sub i hi)
  have hs₁ := I₁.scr
  obtain hD : ∀ i ∈ [DX, DY, DZ], c.sl i ∈ rcbW c.rcbSlots (c.pt DX DY DZ) ++ sumR.map c.sl := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simp [rcbW, Cfg.pt]
  refine WP.block_append (WP.mono (copySl_ok hc hs₁ (o := RX) (a := DX) (by decide) (by decide) (by decide))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_)
  obtain hs₂ := hs₁.of_rest k₂ (by decide)
  refine WP.block_append (WP.mono (copySl_ok hc hs₂ (o := RY) (a := DY) (by decide) (by decide) (by decide))
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_)
  obtain hs₃ := hs₂.of_rest k₃ (by decide)
  refine WP.mono (copySl_ok hc hs₃ (o := RZ) (a := DZ) (by decide) (by decide) (by decide))
    fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  obtain o : ∀ {s s' : State} {j i : Nat}, Outside base (c.sl j) (8 * c.n) s.mem s'.mem → i < 45 → i ≠ j →
      sv c base s' i = sv c base s i := fun O hi hij => sv_out O h7 hn hi hij
  obtain x₄ : sv c base s₄ RX = sv c base s₁ DX := by
    rw [o O₄ (by decide) (by decide), o O₃ (by decide) (by decide), e₂]
  obtain y₄ : sv c base s₄ RY = sv c base s₁ DY := by
    rw [o O₄ (by decide) (by decide), e₃, o O₂ (by decide) (by decide)]
  obtain z₄ : sv c base s₄ RZ = sv c base s₁ DZ := by
    rw [e₄, o O₃ (by decide) (by decide), o O₂ (by decide) (by decide)]
  obtain K₄ : Rest [.r4] s₁ s₄ := k₂.trans (k₃.trans k₄)
  obtain U₄ : Unch base (slWk c sumW) s.mem s₄.mem := by
    have := ((Outs.unch PK.mem).trans (O₂.unch.trans (O₃.unch.trans O₄.unch)))
    refine this.mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · simp only [progW, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with ⟨y, hy, rfl⟩ | hw | hw
      · simp only [rcbW, Cfg.rcbSlots, Cfg.pt, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [MP'_n]
      · subst hw; simp [MP'_n, MP'_tmp]
      · subst hw; exact List.mem_append_right _ (List.mem_singleton_self _)
    · simp only [List.mem_append, List.mem_singleton] at hw
      rcases hw with hw | hw | hw <;> (subst hw; simp)
  refine ⟨hs₃.of_rest k₄ (by decide), PK.rest.trans (K₄.mono (by decide)), U₄, ?_, ?_, ?_⟩
  · have hM₁ := I₁.mod
    refine ⟨hM₁.n0, hM₁.mo, hM₁.tmp, hM₁.sep, ?_, hM₁.inv, hM₁.red⟩
    rw [U₄.wordsVal (fun w hw => ?_) (by have := hM₁.mo; omega_using [hn, this])]
    · exact hM.val
    · exact apart_slWk (c := c) h7 (i := MP) (by decide) (by decide) w hw
  · rw [z₄]; exact I₁.lt _ (hD DZ (by simp))
  · have vx := I₁.val _ (hD DX (by simp))
    obtain vy := I₁.val _ (hD DY (by simp))
    obtain vz := I₁.val _ (hD DZ (by simp))
    show (toM _ _ (sv c base s₄ RX), toM _ _ (sv c base s₄ RY), toM _ _ (sv c base s₄ RZ)) = _
    rw [x₄, y₄, z₄]
    exact (congrArg₂ Prod.mk vx (congrArg₂ Prod.mk vy vz)).trans t₁

/-- `Step` depends only on what the slots of `a`, `3b` and `G` stand for. -/
theorem Step.congr {L : LadderCfg} {C : Curve} {base : Addr} {s s' : State} {k : Nat}
    {Q : Nat → Fe C → Fe C → Fe C → Prop} {a0 : Bool} (h : Step L C base s k Q a0)
    (ha : tmv C L.M.n base s' L.S.a = tmv C L.M.n base s L.S.a)
    (hb : tmv C L.M.n base s' L.S.b3 = tmv C L.M.n base s L.S.b3)
    (hx : tmv C L.M.n base s' L.G.x = tmv C L.M.n base s L.G.x)
    (hy : tmv C L.M.n base s' L.G.y = tmv C L.M.n base s L.G.y)
    (hz : tmv C L.M.n base s' L.G.z = tmv C L.M.n base s L.G.z) : Step L C base s' k Q a0 := by
  intro j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3
  rw [ha, hb] at h2
  rw [ha, hb, hx, hy, hz] at h3
  exact h j hj X Y Z X2 Y2 Z2 X3 Y3 Z3 hq h2 h3

/-- After `[u]G + [v]Q`, for the invariants `Q₁` of the signature's ladder
and `Q₂` of ECDH's: `R` holds the complete addition of what they end with. -/
structure Pts (c : Cfg) (s₀ : State) (base : Addr)
    (Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop) (s : State) : Prop where
  scr : Scr s base size
  far : Far s base 8192
  rest : Rest (.lr :: work) s₀ s
  fixed : Fixed c base s₀.gpr s.mem
  t₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0
  flag : flagW c base s =
    mask32 (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧ (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n))
  rm_lt : sv c base s RM' < c.C.n
  rm : toM c.C.n (2 ^ (64 * c.n)) (sv c base s RM') = Fin.ofNat c.C.n (sigR c s₀)
  rz_lt : sv c base s RZ < c.C.p
  pt : ∃ X1 Y1 Z1 X2 Y2 Z2 : Fe c.C, Q₁ 0 X1 Y1 Z1 ∧ Q₂ 0 X2 Y2 Z2 ∧
    (tmv c.C c.n base s (c.sl RX), tmv c.C c.n base s (c.sl RY), tmv c.C c.n base s (c.sl RZ)) =
      rcbAdd (Fin.ofNat c.C.p c.C.a) (Fin.ofNat c.C.p (3 * c.C.b)) X1 Y1 Z1 X2 Y2 Z2
  unch : Unch base [(0, 8192)] s₀.mem s.mem

/-- Where `scalarAt` writes: the table of bits, or `K`'s slot. -/
abbrev scW (c : Cfg) : List (Nat × Nat) := [(bitsAt c.n 0, 64 * c.n), (c.sl K, 8 * c.n)]

/-- The scalar at slot `i` to where the multiplications read it: `K`'s slot
(for the call), or the table of its bits (for the ladder). -/
theorem scalarAt_ok (hc : CfgOk c) {s : State} {base : Addr} (hs : Scr s base size) (hf : Far s base 8192)
    {i : Nat} (hi : i < 45) (hiK : i ≠ K) :
    WP isa (Impl.Ecdsa.Verify.Arm.Cfg.scalarAt c i) s fun s' => Rest [.r4, .r5, .r7, .r11] s s' ∧
      Unch base (scW c) s.mem s'.mem ∧ (c.mul.isSome → sv c base s' K = sv c base s i) ∧
      (c.mul = none → ∀ t < 64 * c.n, s'.mem (off base (bitsAt c.n 0 + t)) =
        if (sv c base s i).testBit t then 1 else 0) := by
  unfold Impl.Ecdsa.Verify.Arm.Cfg.scalarAt
  cases hm : c.mul with
  | none =>
    simp only
    exact WP.mono (tbl_bits_ok hc hs hf (i := i) (j := 0) hi (by decide)) fun s' ⟨b, k, O⟩ =>
      ⟨k, O.unch.mono fun w hw => by rw [List.mem_singleton.mp hw]; exact List.mem_cons_self,
        fun h => absurd h (by simp), fun _ => b⟩
  | some C =>
    simp only
    exact WP.mono (copySl_ok hc hs (o := K) (a := i) (by decide) hi (Ne.symm hiK)) fun s' ⟨e, k, O⟩ =>
      ⟨k.mono (by simp), O.unch.mono fun w hw => by
        rw [List.mem_singleton.mp hw]; exact List.mem_cons_of_mem _ List.mem_cons_self,
        fun _ => e, fun h => absurd h (by simp)⟩

theorem apart_scW (h7 : c.n < 10) {i : Nat} (hi : i < 45) (hiK : i ≠ K) :
    ∀ w ∈ scW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact apart_tbl h7 hi 0 _ (List.mem_singleton_self _)
  · exact sl_apart c hiK

theorem fixedOk_scW (h7 : c.n < 10) : FixedOk c (scW c) := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact fixedOk_tbl h7 0 _ (List.mem_singleton_self _)
  · exact fixedOk_slW (l := [K]) (by decide) _ (List.mem_singleton_self _)

theorem tbl_apart_scW (h7 : c.n < 10) {t : Nat} (ht : t < 64 * c.n) :
    ∀ w ∈ scW c, bitsAt c.n 1 + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n 1 + t := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact tbl_apart_tbl (by decide) ht _ (List.mem_singleton_self _)
  · exact tbl_apart_slW h7 (l := [K]) (by decide) 1 t _ (List.mem_singleton_self _)

theorem scW_le (h7 : c.n < 10) : ∀ w ∈ scW c, w.1 + w.2 ≤ 8192 := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact tbl_le h7
  · have := sl_le c h7 (i := K) (by decide); dsimp only [size] at this ⊢; omega_using [this]

/-- The slots the two ladders and `save` write. -/
abbrev ptsW : List Nat :=
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ, TMP, UX, UY, UZ, K, ACC, PT]

theorem acc_pt_ptsW {i : Nat} (hl : i ∉ ptsW) : i ∉ [ACC, PT] := fun h => hl (by
  rcases List.mem_cons.mp h with rfl | h
  · decide
  · rw [List.mem_singleton.mp h]; decide)

theorem k_ptsW {i : Nat} (hl : i ∉ ptsW) : i ≠ K := fun h => hl (by rw [h]; decide)

/-- `[u]G + [v]Q`, into `R`. -/
theorem pointsWith_ok (hc : CfgOk c) {s₀ : State} {base : Addr} {s : State}
    (hM : Mid c s₀ base s) {generator : Prog isa} {Q₁ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop}
    {a0₁ : Bool} (hMul : GeneratorWP c generator s₀ base (sv c base s U) Q₁ s.syms a0₁)
    (hstep₁ : Step c.ladderCfg c.C base s (sv c base s U) Q₁ a0₁) (hO₁ : Q₁ (8 * c.C.len) 0 1 0)
    (hC : Law c.C) {P : Point c.C} (hPc : onCurve c.C P = true)
    (hQP : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) 1 P)
    (hv : sv c base s V < 2 ^ (8 * c.C.len)) {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts c s₀ base Q₁ (fun j X Y Z => Rep c.C X Y Z (mul (sv c base s V >>> j) P)) s' →
      WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.Arm.Cfg.pointsWith c generator) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  unfold Impl.Ecdsa.Verify.Arm.Cfg.pointsWith
  refine WP.seq ?_
  -- `u` to where `[u]G` reads it.
  refine WP.seq (WP.mono_syms (scalarAt_ok hc hM.scr hM.far (i := U) (by decide) (by decide))
    fun s₁ ⟨k₁, U₁, kk₁, b₁⟩ syms₁ => ?_)
  obtain hs₁ := hM.scr.of_rest k₁ (by decide)
  obtain hf₁ := hM.far.of_rest k₁
  obtain F₁ := F.unch h7 hn (fixedOk_scW h7) U₁
  obtain v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hiK =>
    sv_unch U₁ h7 hn hi (apart_scW h7 hi hiK)
  -- `[u]G`.
  obtain hlt₁ : ∀ x ∈ ladR c.ladderCfg, wordsVal s₁.mem base x c.MP'.n < c.C.p := by
    intro x hx
    have hx' : x ∈ [AP, B3P, GX, GY, ONEP, RX, RY, RZ].map c.sl := hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    show sv c base s₁ i < c.C.p
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₁.ap (hmont _)
    · exact lt_of_eq_of_lt F₁.b3p (hmont _)
    · exact lt_of_eq_of_lt F₁.gx (hmont _)
    · exact lt_of_eq_of_lt F₁.gy (hmont _)
    · exact lt_of_eq_of_lt F₁.onep (Nat.mod_lt _ (by omega_arith))
    · rw [v₁ (by decide) (by decide), hM.rx]; omega_arith
    · rw [v₁ (by decide) (by decide), hM.ry]; exact hmont _
    · rw [v₁ (by decide) (by decide), hM.rz]; omega_arith
  obtain tv₁ : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hiK => by
      show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _)
      rw [v₁ hi hiK]
  obtain hR₁ : Q₁ c.ladderCfg.nbits (tmv c.C c.n base s₁ (c.sl RX)) (tmv c.C c.n base s₁ (c.sl RY))
      (tmv c.C c.n base s₁ (c.sl RZ)) := by
    show Q₁ (8 * c.C.len) (toM _ _ (sv c base s₁ RX)) (toM _ _ (sv c base s₁ RY)) (toM _ _ (sv c base s₁ RZ))
    rw [v₁ (by decide) (by decide), v₁ (by decide) (by decide), v₁ (by decide) (by decide), hM.rx, hM.ry,
      hM.rz, toM_cmont hc, toM_zero]
    exact hO₁
  refine WP.seq (WP.mono (hMul s₁ hs₁ hf₁ F₁ hlt₁
    (Step.congr hstep₁ (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide))
      (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide)) (tv₁ (by decide) (by decide))) hR₁
    (by rw [v₁ (by decide) (by decide), hM.rx]) (by rw [v₁ (by decide) (by decide), hM.ry])
    (by rw [v₁ (by decide) (by decide), hM.rz]) b₁ kk₁
    (hM.rest.trans (k₁.mono (by simp [work])))
    (whole_of' hM.unch U₁ (scW_le h7))
    syms₁)
    fun s₂ ⟨K₂, U₂, M₂, L₂, q₂⟩ => ?_)
  rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at U₂
  obtain hs₂ := hs₁.of_rest K₂ (by decide)
  obtain F₂ := F₁.unch h7 hn ((fixedOk_slWkP h7 (by decide)).append (fixedOk_genX h7)) U₂
  -- `U = [u]G`, `R = O`.
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  obtain F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  obtain sub₂ : ∀ i ∈ [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ,
      TMP], i ∈ ptsW := by decide
  obtain sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  obtain W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₃ i = sv c base s i := fun {i} hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_append (apart_slWkP h7 hi (fun h => hl (sub₂ _ h)))
        (apart_genX h7 hi (acc_pt_ptsW hl))))).trans (v₁ hi (k_ptsW hl))
  obtain hf₃ := (hf₁.of_rest K₂).of_rest k₃
  -- `v` to where `[v]Q` reads it.
  refine WP.seq (WP.mono (scalarAt_ok hc hs₃ hf₃ (i := V) (by decide) (by decide))
    fun s₄ ⟨k₄, U₄, kk₄, b₄⟩ => ?_)
  obtain hs₄ := hs₃.of_rest k₄ (by decide)
  obtain hf₄ := hf₃.of_rest k₄
  obtain F₄ := F₃.unch h7 hn (fixedOk_scW h7) U₄
  obtain v₄ : ∀ {i}, i < 45 → i ≠ K → sv c base s₄ i = sv c base s₃ i := fun hi hiK =>
    sv_unch U₄ h7 hn hi (apart_scW h7 hi hiK)
  obtain hV : sv c base s₃ V = sv c base s V := W₃ (by decide) (by decide)
  -- `[v]Q`.
  obtain tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv c.C c.n base s₄ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hl => by
      show toM _ _ (sv c base s₄ _) = toM _ _ (sv c base s _)
      rw [v₄ hi (k_ptsW hl), W₃ hi hl]
  refine WP.seq (WP.mono (qMul_ok hc hC hs₄ hf₄ F₄ (px := PX) (py := PY) (by decide)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide) (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by rw [v₄ (by decide) (by decide), rx₃]) (by rw [v₄ (by decide) (by decide), ry₃])
    (by rw [v₄ (by decide) (by decide), rz₃]) hPc
    (by rw [tv₄ (by decide) (by decide), tv₄ (by decide) (by decide)]; exact hQP) hv
    (fun hm => by rw [kk₄ hm, hV]) (fun hm t ht => by rw [b₄ hm t ht, hV]))
    fun s₅ ⟨K₅, U₅, M₅, L₅, q₅'⟩ => ?_)
  obtain q₅ : Rep c.C (tmv c.C c.n base s₅ (c.sl RX)) (tmv c.C c.n base s₅ (c.sl RY))
      (tmv c.C c.n base s₅ (c.sl RZ)) (mul (sv c base s V >>> 0) P) := by
    rw [Nat.shiftRight_zero]; exact q₅'
  rw [VG.Proof.Weierstrass.Arm.Point.ladWp, ladWx_eq] at U₅
  obtain hs₅ := hs₄.of_rest K₅ (by decide)
  obtain F₅ := F₄.unch h7 hn ((fixedOk_slWkP h7 (by decide)).append (fixedOk_genX h7)) U₅
  obtain v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv c base s₅ i = sv c base s₄ i := fun {i} hi hl =>
    sv_unch U₅ h7 hn hi (apart_append (apart_slWkP h7 hi (fun h => hl (sub₂ _ h)))
      (apart_genX h7 hi (acc_pt_ptsW hl)))
  -- The sum.
  obtain u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv c base s₅ i = sv c base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_append (apart_slWkP h7 (by decide) (by decide))
        (apart_genX h7 (by decide) (by decide)))).trans (v₄ (by decide) (by decide))
  refine WP.mono (sum_ok hc hs₅ (hf₄.of_rest K₅) M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, g₆, U₆, M₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact lt_of_eq_of_lt F₅.ap (hmont _)
    · exact lt_of_eq_of_lt F₅.b3p (hmont _)
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (List.mem_cons_self ..)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · rw [u₅ (by decide), uz₃]
      exact L₂ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
    · exact L₅ _ (List.mem_cons_self ..)
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact L₅ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  obtain F₆ := F₅.unch h7 hn (fixedOk_slWk h7 (by decide)) U₆
  obtain sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  obtain UW : Unch base ((scW c ++ slWkP c ptsW) ++ genX c) s.mem s₆.mem := by
    obtain hsl : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slWk c l,
        w ∈ (scW c ++ slWkP c ptsW) ++ genX c := fun hl w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
          (List.mem_append_left _ (List.mem_map_of_mem (hl i hi)))))
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ hw)))
    obtain hslP : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ ptsW) → ∀ w ∈ slWkP c l,
        w ∈ (scW c ++ slWkP c ptsW) ++ genX c := fun hl w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact hsl hl w hw
      · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_right _ hw))
    refine (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆))))).mono fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact hslP sub₂ w hw
      · exact List.mem_append_right _ hw
    rcases List.mem_append.mp hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_map_of_mem (sub₃ i hi)))))
    rcases List.mem_append.mp hw with hw | hw
    · exact List.mem_append_left _ (List.mem_append_left _ hw)
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact hslP sub₂ w hw
      · exact List.mem_append_right _ hw
    · exact hsl sub₆ w hw
  obtain tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv c base s₃ i = sv c base s₂ j →
      tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s₂ (c.sl j) := fun hi _ e => by
    show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s₂ _)
    rw [u₅ hi, e]
  obtain tR₅ : ∀ {i}, i ∈ [AP, B3P] → tmv c.C c.n base s₅ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun {i} hi => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      show toM _ _ (sv c base s₅ _) = toM _ _ (sv c base s _)
      rcases hi with rfl | rfl <;> rw [v₅ (by decide) (by decide), v₄ (by decide) (by decide),
        W₃ (by decide) (by decide)]
  obtain ha : tmv c.C c.n base s (c.sl AP) = Fin.ofNat c.C.p c.C.a := by
    show toM _ _ (wordsVal s.mem base (c.sl AP) c.n) = _
    rw [F.ap]; exact toM_cmont hc _
  obtain hb : tmv c.C c.n base s (c.sl B3P) = Fin.ofNat c.C.p (3 * c.C.b) := by
    show toM _ _ (wordsVal s.mem base (c.sl B3P) c.n) = _
    rw [F.b3p]; exact toM_cmont hc _
  obtain hFl := sl_le c h7 (i := FLAG) (by decide)
  obtain apF : ∀ w ∈ (scW c ++ slWkP c ptsW) ++ genX c, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
    intro w hw
    rcases apart_append (apart_append (apart_scW (c := c) h7 (i := FLAG) (by decide) (by decide))
      (apart_slWkP (c := c) h7 (i := FLAG) (by decide) (by decide)))
      (apart_genX (c := c) h7 (i := FLAG) (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h
  obtain rm₆ : sv c base s₆ RM' = sv c base s RM' :=
    sv_unch UW h7 hn (by decide) (apart_append (apart_append (apart_scW h7 (by decide) (by decide))
      (apart_slWkP h7 (by decide) (by decide))) (apart_genX h7 (by decide) (by decide)))
  obtain Kw : Rest work s s₆ := (k₁.mono (by decide)).trans ((K₂.mono powClob_work).trans ((k₃.mono (by decide)).trans
    ((k₄.mono (by decide)).trans ((K₅.mono powClob_work).trans (g₆.mono callClob_work)))))
  refine ⟨hs₆, hM.far.of_rest Kw, hM.rest.trans (Kw.mono (by simp)), F₆, fun t ht => ?_,
    by rw [flagW, Unch.readW32 UW apF (by omega_arith), ← flagW]; exact hM.flag,
    by rw [rm₆]; exact hM.rm_lt, by rw [rm₆]; exact hM.rm, rz₆,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, tR₅ (by decide), tR₅ (by decide), ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]⟩, ?_⟩
  · rw [tbl_unch UW h7 (j := 1) (by decide) ht (apart_append (apart_append (tbl_apart_scW h7 ht)
      (tbl_apart_slWkP h7 (by decide))) (tbl_apart_genX h7 (by decide) ht))]
    exact hM.t₁ t ht
  · refine whole_of' hM.unch UW fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact scW_le h7 w hw
      · have := slWkP_le h7 (by decide) w hw; dsimp only [size] at this; omega_arith
    · exact genX_le h7 w hw

end VG.Proof.Ecdsa.Verify.Arm

end

end


/-!
# ECDSA verification on 32-bit ARM: `x` and the result

As on x86 (`Proof/Ecdsa/Verify/X86/Final.lean`).

`vtail_ok`: from what `pointsWith_ok` leaves, the signature's power gives
`Z^(p-2)`, and `final` computes `x = X Z^(p-2)` out of Montgomery's form,
`x R mod n` and `x R - r R mod n`, ands the masks of `Z ≠ 0` and of that
difference being zero (`x ≡ r` modulo `n`) into the flag, returns its low
bit and restores the callee-saved registers (`vfinish_ok`, the signature's
`tail_ok`). It writes only the working space.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.Verify.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.Arm VG.Proof.Ecdh.Arm
open VG.Proof.X25519.Arm (Rest wp_ldr wp_dp op2_imm dpVal)
open VG.Impl.Ecdsa.Verify.Arm (RM' XN W)

variable {c : Cfg}

theorem vfinish_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.finish c =
    .ldr .r10 wb (c.sl FLAG) :: .dp .and .r0 .r10 (.imm 1) :: Cfg.restore := rfl

/-- The return value and the callee-saved registers. -/
theorem vfinish_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 32} (hsv : ∀ rd ∈ Cfg.saved, s.mem.readW (off base rd.2) 32 = g rd.1) (b : Bool)
    (hf : flagW c base s = mask32 (b = true)) :
    WP isa (.block (Impl.Ecdsa.Verify.Arm.Cfg.finish c)) s fun s' =>
      s'.mem = s.mem ∧ s'.gpr .r0 = (if b then 1 else 0) ∧
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = g rd.1) ∧ s'.sp = s.sp := by
  obtain hF := sl_le c hc.n10 (i := FLAG) (by decide)
  have := hc.n0
  have hsz : size = 4096 := rfl
  rw [vfinish_eq]
  refine wp_ldr (hs.off_lt (by omega_using [hF, this])) (hs.ea (by omega_using [hF, this])) (hs.read (d := c.sl FLAG) (n := 4) (by omega_using [hF, this]))
    fun s₁ u₁ => ?_
  obtain hs₁ := hs.of_rest (u₁.rest (ws := [.r10]) (by simp)) (by decide)
  obtain hc₁ : s₁.gpr .r10 = mask32 (b = true) := by rw [u₁.gpr, ← flagW, hf]
  refine wp_dp (op2_imm (by decide)) fun s₂ u₂ => ?_
  obtain hs₂ := hs₁.of_rest (u₂.rest (ws := [.r0]) (by simp)) (by decide)
  obtain r0₂ : s₂.gpr .r0 = if b then 1 else 0 := by rw [u₂.gpr, dpVal, hc₁]; exact mask_bit b
  rw [restore_eq]
  refine WP.mono (ldrs_ok hs₂ Cfg.saved (fun p hp => by have := saved_lt p hp; omega_using [hsz, this]) saved_nodup
    (fun p hp => (saved_r12 p hp).1)) fun s' ⟨m', K', V'⟩ =>
      ⟨by rw [m', u₂.mem, u₁.mem], by rw [K'.gpr _ (by decide), r0₂],
        fun rd hrd => by rw [V' rd hrd, u₂.mem, u₁.mem, hsv rd hrd], by rw [K'.sp, u₂.sp, u₁.sp]⟩

theorem final_eq (c : Cfg) : Impl.Ecdsa.Verify.Arm.Cfg.final c =
    .seq (Mont.mulCall c.SP (c.sl XM) (c.sl RX) (c.sl ACC) c.umaal)
    (.seq (Mont.mulCall c.SP (c.sl X) (c.sl XM) (c.sl ONE) c.umaal)
    (.seq (Mont.mulCall c.SN (c.sl XN) (c.sl X) (c.sl R2N) c.umaal)
    (.seq (Mont.subCall c.SN (c.sl W) (c.sl XN) (c.sl RM') c.umaal)
      (.block (c.checkNonzero (c.sl RZ) ++ (Impl.Ecdh.Arm.Cfg.checkZero c (c.sl W) ++
        Impl.Ecdsa.Verify.Arm.Cfg.finish c)))))) := by
  simp only [Impl.Ecdsa.Verify.Arm.Cfg.final, progs, List.append_assoc]

/-- The slots `vtail_ok` writes. -/
abbrev finW : List Nat := [ACC, PT, TMP, XM, X, XN, W]

/-- `Z^(p-2)`, `x`, the last checks and the result. -/
theorem vtail_ok (hc : CfgOk c) {s₀ : State} {base : Addr}
    {Q₁ Q₂ : Nat → Fe c.C → Fe c.C → Fe c.C → Prop} {s : State} (hP : Pts c s₀ base Q₁ Q₂ s) :
    WP isa (.seq (pow c.powP c.SP c.umaal) (Impl.Ecdsa.Verify.Arm.Cfg.final c)) s fun s' =>
      (∀ rd ∈ Cfg.saved, s'.gpr rd.1 = s₀.gpr rd.1) ∧ s'.sp = s₀.sp ∧
      Unch base [(0, 8192)] s₀.mem s'.mem ∧ ∃ xo, xo < c.C.p ∧
        Fin.ofNat c.C.p xo = tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) ∧
        s'.gpr .r0 = if (KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
          (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
          Fin.ofNat c.C.n xo = Fin.ofNat c.C.n (sigR c s₀) then 1 else 0 := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hP.scr.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  obtain hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hn3 := hc.n_ge
  have F := hP.fixed
  obtain hf : c.sl FLAG + 4 ≤ size := by have := sl_le c h7 (i := FLAG) (by decide); omega_using [h0, this]
  obtain henc : encodable (BitVec.ofNat 32 (64 * c.n)) = true := by
    have : ∀ n < 10, encodable (BitVec.ofNat 32 (64 * n)) = true := by decide
    exact this _ h7
  -- `Z^(p-2)`.
  refine WP.seq (WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) (powWkP hc) hc.fp hpR
    (bitsAt_lt hc (j := 1) (by decide)) hP.scr hP.far (modP_of hc F.mp) hP.rz_lt F.onep hP.t₁ (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_using [this]) henc)
    fun s₁ ⟨K₁, U₁, lt₁, v₁⟩ => ?_)
  rw [powWxP_eq] at U₁
  obtain hs₁ := hP.scr.of_rest K₁ (by decide)
  obtain hf₁ := hP.far.of_rest K₁
  obtain F₁ := F.unch h7 hn (fixedOk_slWk h7 (by decide)) U₁
  obtain e₁ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₁ i = sv c base s i := fun hi hl =>
    sv_unch U₁ h7 hn hi (apart_slWk h7 hi hl)
  rw [final_eq]
  -- `XM = X · ACC`.
  obtain hM₁ := modP_of hc F₁.mp
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs₁ hf₁ (o := XM) (a := RX) (b := ACC) (by decide) (by decide) (by decide) lt₁) fun s₂ ⟨k₂, _, e₂⟩ => ?_)
  obtain hs₂ := k₂.scr hs₁
  obtain hf₂ := hf₁.of_rest k₂.rest
  obtain M₂ := hM₁.keepArm (j := MP) (by decide) rfl rfl rfl rfl h7 hn k₂ (by decide) (by decide)
  obtain v₂ : ∀ {i}, i < 45 → i ≠ XM → i ≠ TMP → sv c base s₂ i = sv c base s₁ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₂ hi h₁ h₂
  -- `X = XM · 1`.
  obtain one₂ : sv c base s₂ ONE = 1 := (v₂ (by decide) (by decide) (by decide)).trans F₁.one
  refine WP.seq (WP.mono (slMul_ok hc.fp (MP'_n c) h7 hs₂ hf₂ (o := X) (a := XM) (b := ONE) (by decide) (by decide) (by decide) (by rw [one₂]; omega_using [hp3])) fun s₃ ⟨k₃, lt₃, e₃⟩ => ?_)
  obtain hs₃ := k₃.scr hs₂
  obtain hf₃ := hf₂.of_rest k₃.rest
  obtain v₃ : ∀ {i}, i < 45 → i ≠ X → i ≠ TMP → sv c base s₃ i = sv c base s₂ i := fun hi h₁ h₂ =>
    sv_keep (MP'_n c) rfl h7 hn k₃ hi h₁ h₂
  obtain x₃ : Fin.ofNat c.C.p (sv c base s₃ X) =
      tmv c.C c.n base s (c.sl RX) * tmv c.C c.n base s (c.sl RZ) ^ (c.C.p - 2) := by
    have acc₁ : toM c.C.p (2 ^ (64 * c.n)) (sv c base s₁ ACC) =
        toM c.C.p (2 ^ (64 * c.n)) (sv c base s RZ) ^ (c.C.p - 2) := v₁
    rw [toM_one_mul hpR (by rw [e₃, one₂]), toM_mul hpR e₂, acc₁]
    show toM _ _ (sv c base s₁ RX) * _ = toM _ _ (sv c base s RX) * toM _ _ (sv c base s RZ) ^ _
    rw [e₁ (by decide) (by decide)]
  -- `XN = x R mod n`, `W = XN - r R mod n`.
  obtain hMN₃ := modN_of hc (show wordsVal s₃.mem base (c.sl MN) c.n = c.C.n from
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.mn)))
  obtain r2₃ : sv c base s₃ R2N = 2 ^ (64 * c.n) * 2 ^ (64 * c.n) % c.C.n :=
    (v₃ (by decide) (by decide) (by decide)).trans ((v₂ (by decide) (by decide) (by decide)).trans
      ((e₁ (by decide) (by decide)).trans F.r2n))
  refine WP.seq (WP.mono (slMul_ok hc.fn (MN'_n c) h7 hs₃ hf₃ (o := XN) (a := X) (b := R2N) (by decide) (by decide) (by decide) (by rw [r2₃]; exact Nat.mod_lt _ (by omega_using [hn3])))
    fun s₄ ⟨k₄, lt₄, e₄⟩ => ?_)
  obtain hs₄ := k₄.scr hs₃
  obtain hf₄ := hf₃.of_rest k₄.rest
  obtain M₄ := hMN₃.keepArm (j := MN) (by decide) rfl rfl rfl rfl h7 hn k₄ (by decide) (by decide)
  obtain v₄ : ∀ {i}, i < 45 → i ≠ XN → i ≠ TMP → sv c base s₄ i = sv c base s₃ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₄ hi h₁ h₂
  obtain rm₄ : sv c base s₄ RM' = sv c base s RM' := by
    rw [v₄ (by decide) (by decide) (by decide), v₃ (by decide) (by decide) (by decide),
      v₂ (by decide) (by decide) (by decide), e₁ (by decide) (by decide)]
  refine WP.seq (WP.mono (slSub_ok hc.fn (MN'_n c) h7 hs₄ hf₄ (o := W) (a := XN) (b := RM') (by decide) (by decide) (by decide) lt₄ (by rw [rm₄]; exact hP.rm_lt)) fun s₅ ⟨k₅, e₅⟩ => ?_)
  obtain hs₅ := k₅.scr hs₄
  obtain hf₅ := hf₄.of_rest k₅.rest
  obtain v₅ : ∀ {i}, i < 45 → i ≠ W → i ≠ TMP → sv c base s₅ i = sv c base s₄ i := fun hi h₁ h₂ =>
    sv_keep (MN'_n c) rfl h7 hn k₅ hi h₁ h₂
  obtain w₅ : sv c base s₅ W = 0 ↔ Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀) := by
    obtain hlt : sv c base s₅ W < c.C.n := by rw [e₅]; exact Nat.mod_lt _ (by omega_using [hn3])
    rw [← toM_eq_zero_iff hnR hlt, e₅, toM_sub (by rw [rm₄]; have := hP.rm_lt; omega_using [this]), rm₄, hP.rm,
      toM_r2 hnR (by rw [e₄, r2₃])]
    constructor <;> intro h <;> grind
  -- What changed: `finW` and the accumulator.
  obtain hsub : ∀ {l : List Nat}, (∀ i ∈ l, i ∈ finW) → ∀ w, w ∈ slW c l ∨ w ∈ [(c.wk, 64 * c.n)] →
      w ∈ slWk c finW := fun hl w hw => by
    rcases hw with hw | hw
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact List.mem_append_left _ (List.mem_map_of_mem (hl i hi))
    · exact List.mem_append_right _ hw
  obtain U₅ : Unch base (slWk c finW) s.mem s₅.mem :=
    (U₁.trans ((unch_slots (MP'_n c) rfl k₂.unchOne (l := [XM, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MP'_n c) rfl k₃.unchOne (l := [X, TMP]) (by simp) (by simp)).trans
      ((unch_slots (MN'_n c) rfl k₄.unchOne (l := [XN, TMP]) (by simp) (by simp)).trans
      (unch_slots (MN'_n c) rfl k₅.unchOne (l := [W, TMP]) (by simp) (by simp)))))).mono fun w hw => by
      simp only [List.mem_append] at hw
      rcases hw with hw | hw | hw | hw | hw
      all_goals exact hsub (by decide) w hw
  -- The checks and the result.
  rw [WP.block_append_iff]
  refine WP.mono (checkNonzero_ok c hs₅ h0 (sl_le c h7 (i := RZ) (by decide)) hf) fun s₆ ⟨f₆, k₆, O₆⟩ => ?_
  obtain hs₆ := hs₅.of_rest k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (checkZero_ok c hs₆ h0 (sl_le c h7 (i := W) (by decide)) hf) fun s₇ ⟨f₇, k₇, O₇⟩ => ?_
  obtain hs₇ := hs₆.of_rest k₇ (by decide)
  obtain UW : Unch base (slWk c finW ++ [(c.sl FLAG, 4)]) s.mem s₇.mem := by
    have := U₅.trans (O₆.unch.trans O₇.unch)
    exact this.mono fun w hw => by
      rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_right _ hw
        · exact List.mem_append_right _ hw
  obtain F₇ := F.unch h7 hn ((fixedOk_slWk h7 (by decide)).append fixedOk_flag) UW
  obtain z₅ : wordsVal s₅.mem base (c.sl RZ) c.n = sv c base s RZ := by
    show sv c base s₅ RZ = _
    rw [v₅ (by decide) (by decide) (by decide), v₄ (by decide) (by decide) (by decide),
      v₃ (by decide) (by decide) (by decide), v₂ (by decide) (by decide) (by decide),
      e₁ (by decide) (by decide)]
  obtain hW₆ : wordsVal s₆.mem base (c.sl W) c.n = sv c base s₅ W :=
    sv_flag O₆ h0 h7 hn (by decide) (by decide)
  obtain hflag : flagW c base s₇ = mask32 (decide ((KeyOk c s₀ ∧ (0 < sigR c s₀ ∧ sigR c s₀ < c.C.n) ∧
      (0 < sigS c s₀ ∧ sigS c s₀ < c.C.n)) ∧ sv c base s RZ ≠ 0 ∧
      Fin.ofNat c.C.n (sv c base s₃ X) = Fin.ofNat c.C.n (sigR c s₀)) = true) := by
    rw [f₇, f₆, hW₆, flagW, flag_unch U₅ h7 h0 hn (by decide), ← flagW, hP.flag, z₅, mask32_and, mask32_and]
    simp only [w₅, decide_eq_true_eq, and_assoc]
  refine WP.mono (vfinish_ok hc hs₇ F₇.saved _ hflag) fun s' ⟨hm, ret, saved, sp⟩ =>
    ⟨saved, ?_, ?_, _, lt₃, x₃, ?_⟩
  · rw [sp, k₇.sp, k₆.sp, k₅.rest.sp, k₄.rest.sp, k₃.rest.sp, k₂.rest.sp, K₁.sp, hP.rest.sp]
  · rw [hm]
    exact whole_of hP.unch UW (le_append (slWk_le h7 (by decide)) (flag_le h0 h7))
  · rw [ret]
    simp only [decide_eq_true_eq]

end VG.Proof.Ecdsa.Verify.Arm
