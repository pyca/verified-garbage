import VerifiedGarbage.Proof.Ecdh.X86.JacPow

/-! # ECDH correctness with the x86 P-256 signed-window multiplier -/
namespace VG.Proof.Ecdh.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86 VG.Proof.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (QY R2P BP QXM QYM W0 W1 W2 W3 PX PY Args.ecdh)
variable {c : Cfg}

theorem exchangeJacWindow_eq (c : Cfg) : Impl.Ecdh.X86.Cfg.exchangeJacWindow c =
    .seq (.seq (.block (c.setupWith Args.ecdh))
      (.seq (bits (c.sl K) (bitsAt c.n 0) (8 * c.n)) (.seq (bits (c.sl EXPP) (bitsAt c.n 1) (8 * c.n))
      (.seq (bits (c.sl EXPN) (bitsAt c.n 2) (8 * c.n)) (.block [])))))
      (.seq (.block (Impl.Ecdh.X86.Cfg.peer c)) (.seq (Impl.Ecdh.X86.Cfg.validate c)
      (.seq (Impl.Ecdh.X86.Cfg.jwinMul c) (.seq c.pPow (Impl.Ecdh.X86.Cfg.middle c))))) :=
  rfl

/-- The stack the parts of `exchangeJacWindow` use. -/
structure EJSp (c : Cfg) : Prop where
  validate : SpOk (Impl.Ecdh.X86.Cfg.validate c) c.stk
  window : SpOk (Impl.Ecdh.X86.Cfg.jwinMul c) c.stk
  pPow : SpOk c.pPow c.stk
  ops : SpOk (ecOps c) c.stk

theorem EJSp.of (h : SpOk (Impl.Ecdh.X86.Cfg.exchangeJacWindow c) c.stk) : EJSp c := by
  rw [exchangeJacWindow_eq] at h
  have h₁ := h.right.right
  have h₂ := h₁.right.right.right
  rw [middle_split] at h₂
  exact ⟨h₁.left, h₁.right.left, h₁.right.right.left, (SpOk.split _ _ _ h₂).1⟩

/-- `vg_ecdh_<curve>` computes the specification's shared secret and restores
the callee-saved registers. -/
theorem exchangeJacWindow_ok (hc : CfgOk c) (hn4 : c.n = 4) (hC : Law c.C) (ham3 : AM3 c.C)
    (hO : PrimeOrder c.C) (hn17 : c.C.n%32=17) (hn64 : 64≤c.C.n)
    (hsp : SpOk (Impl.Ecdh.X86.Cfg.exchangeJacWindow c) c.stk) {s₀ : State} (hp : EPre c s₀) :
    WP isa (Impl.Ecdh.X86.Cfg.exchangeJacWindow c) s₀ fun s' => EKeep c s₀ s' ∧ EPost c s₀ s' := by
  have H := EJSp.of hsp
  have h0 := hc.n0
  have h7 := hc.n10
  have hlhi := hc.len_hi
  have hl8 := hc.len8
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have h4 : (s₀.gpr .esp).toNat + 4 + 4 * 4 ≤ 2 ^ 32 := by have := hp.sp_fit; omega
  rw [exchangeJacWindow_eq]
  refine WP.seq (stage₁ hc hp.setup fun s₂ S₂ => WP.block_nil ?_)
  have hn := S₂.scr.nowrap
  have W₂ : Outside (ptr s₀ 3) 0 size s₀.mem s₂.mem := S₂.ws
  have hq : ∀ t : State, t.gpr .esp = s₂.gpr .esp → t.rd ++ t.wr = s₂.rd ++ s₂.wr →
      Outside (ptr s₀ 3) 0 size s₂.mem t.mem → readSrc t (.mem (Cfg.argOp 2)) = some (arg s₀ 2) :=
    fun t he hrw ho => argLoad_ok (i := 2) ⟨_, by rw [hp.rd]; simp, arg_containsN h4 (by decide)⟩
      (hp.args_sc.sub_left (arg_subN h4 (by decide))) (he.trans S₂.esp)
      (hrw.trans (by rw [S₂.rd, S₂.wr])) (W₂.trans ho)
  -- The peer's key.
  refine WP.seq (WP.mono (peer_ok hc S₂.scr hq hp.peer_fit (by rw [S₂.rd, S₂.wr, hp.rd]; simp) hp.peer_sc
    S₂.fixed.mp) fun s₃ ⟨hs₃, k₃, U₃, r2₃, bp₃, x₃, y₃, f₃⟩ => ?_)
  have F₃ := S₂.fixed.unch h7 hn ((fixedOk_slW (l := [R2P, BP, E, QY]) (by decide)).append fixedOk_flag) U₃
  have e₃ : ∀ {i}, i < 45 → i ∉ [R2P, BP, E, QY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₃ i = sv c (ptr s₀ 3) s₂ i := fun hi hl hf =>
    sv_unch U₃ h7 hn hi (apart_append (apart_slW hl) (apart_flag h0 hf))
  have hq0 : s₂.mem (ptr s₀ 2) = s₀.mem (ptr s₀ 2) := by
    have := keep_of_disjoint' W₂ hp.peer_sc (by omega) (i := 0) (by omega) (by omega)
    rwa [BitVec.add_zero] at this
  -- What the code checks of the peer's key so far.
  have hf₃ : flagW c (ptr s₀ 3) s₃ = mask32 (((s₀.mem (ptr s₀ 2) = 4 ∧
      sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) := by
    rw [f₃, S₂.flag, BitVec.allOnes_and, mask32_and, mask32_and]
    simp only [hq0]
  have hsc : (⟨ptr s₀ 3, size⟩ : Region) ∈ s₀.wr ++ [below (s₀.gpr .esp) c.stk] :=
    List.mem_append_left _ (by rw [hp.wr]; simp)
  have K₃ : Keep c s₀ (ptr s₀ 3) s₃ := ⟨hs₃, by rw [k₃.1 _ (by decide), S₂.esp], by rw [k₃.2.1, S₂.rd],
    by rw [k₃.2.2, S₂.wr], F₃,
    S₂.whole.trans (frame_of_unch U₃ (le_append (slW_le h7 (by decide)) (flag_le h0 h7)) hsc), S₂.sp_lo⟩
  refine WP.seq (K₃.withSp H.validate (WP.mono (validate_ok hc hs₃ F₃ r2₃ bp₃ hf₃)
    fun s₄ ⟨hs₄, g₄, rd₄, wr₄, U₄, f₄, px_lt, py_lt, px, py⟩ w₄ => ?_))
  have F₄ := F₃.unch h7 hn ((fixedOk_slWk (l := [QXM, QYM, TMP, W0, W1, W2, W3, PY]) (by decide)).append
    fixedOk_flag) U₄
  have e₄ : ∀ {i}, i < 45 → i ∉ [QXM, QYM, TMP, W0, W1, W2, W3, PY] → i ≠ FLAG →
      sv c (ptr s₀ 3) s₄ i = sv c (ptr s₀ 3) s₃ i := fun hi hl hf =>
    sv_unch U₄ h7 hn hi (apart_append (apart_slWk hi hl) (apart_flag h0 hf))
  have t₄ : ∀ {j}, j < 3 → ∀ t < 64 * c.n,
      s₄.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) = s₂.mem (off (ptr s₀ 3) (bitsAt c.n j + t)) :=
    fun hj t ht => by
      rw [tbl_unch U₄ h7 hj ht (apart_append (tbl_apart_slWk (by decide) hj ht) (tbl_apart_flag h0 _ t)),
        tbl_unch U₃ h7 hj ht (apart_append (tbl_apart_slW (by decide) _ t) (tbl_apart_flag h0 _ t))]
  -- `[d]P` with signed windows, then `Z^(p-2)`.
  have hQ := peerPt_rep hC _ _ _ px py
  have hQ' : Rep c.C (tmv c.C c.n (ptr s₀ 3) s₄ (c.sl PX))
      (tmv c.C c.n (ptr s₀ 3) s₄ (c.sl PY)) (tmv c.C c.n (ptr s₀ 3) s₄ (c.sl ONEP))
      (peerPt c (s₀.mem (ptr s₀ 2) = 4) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY)) := by
    change Rep c.C _ _ (toM _ _ (wordsVal s₄.mem (ptr s₀ 3) (c.sl ONEP) c.n)) _
    rw [F₄.onep, toM_one hpR]; exact hQ
  have K₄ : Keep c s₀ (ptr s₀ 3) s₄ := ⟨hs₄, by rw [g₄ _ (by decide), K₃.esp], by rw [rd₄, K₃.rd],
    by rw [wr₄, K₃.wr], F₄, w₄, S₂.sp_lo⟩
  refine jwinPow_ok hc hn4 hC ham3 hO hn17 hn64 K₄ H.window H.pPow (peerPt_onCurve hc _ _ _)
    (by unfold peerPt; split <;> intro he <;> cases he) px_lt py_lt hQ'
    (fun t ht => by rw [t₄ (j := 1) (by decide) t ht, S₂.t₁ t ht]) fun s₅ L w₅ => ?_
  have hs₅ := L.scr
  have F₅ := F₄.unch h7 hn ((jwinW_fixed hn4).append fixedOk_pwW)
    L.unch
  have e₅ : ∀ {i}, i < 45 → i ∉ windowSlots → i ∉ [ACC, PT, TMP] →
      sv c (ptr s₀ 3) s₅ i = sv c (ptr s₀ 3) s₄ i :=
    fun hi h₁ h₂ => sv_unch L.unch h7 hn hi (apart_append (jwinW_apart hn4 hi h₁) (apart_pwW hi h₂))
  have hflag₅ : flagW c (ptr s₀ 3) s₅ = mask32 (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
      sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) := by
    have hFl := sl_le c h7 (i := FLAG) (by decide)
    have ap : ∀ w ∈ ecJacW c, c.sl FLAG + 4 ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG := by
      intro w hw
      rcases apart_append (jwinW_apart (c := c) hn4 (i := FLAG) (by decide) (by decide))
        (apart_pwW (c := c) (i := FLAG) (by decide) (by decide)) w hw with h | h
      · exact Or.inl (by omega)
      · exact Or.inr h
    rw [flagW, Unch.readW32 L.unch ap (by omega), ← flagW]
    exact f₄
  have K₅ : Keep c s₀ (ptr s₀ 3) s₅ := ⟨hs₅, by rw [L.gpr _ (by decide), K₄.esp], by rw [L.rd, K₄.rd],
    by rw [L.wr, K₄.wr], F₅, w₅, S₂.sp_lo⟩
  refine WP.mono (middle_ok hc K₅ L.acc_lt hflag₅ H.ops ⟨_, by rw [hp.rd]; simp, arg_containsN h4 (by decide)⟩
    (eArgs_disj hp) hp.out_fit (by rw [hp.wr]; simp) hp.out_sc)
    fun s' ⟨xv, hxl, hxv, bytes, ret, saved, esp, fr⟩ => ⟨⟨saved, esp, fr⟩, ?_⟩
  -- The specification.
  have hlen : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 2 * c.C.len)).length = 2 * c.C.len + 1 := by
    rw [length_bytesAt]; omega
  have hb0 : (Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 2 * c.C.len)).head? = some (s₀.mem (ptr s₀ 2)) := by
    rw [peer_bytes]; rfl
  have hxs : ofBytes (((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 2 * c.C.len)).drop 1).take c.C.len) =
      sv c (ptr s₀ 3) s₃ E := by
    rw [peer_bytes, List.drop_one, List.tail_cons, List.take_left' (length_bytesAt _ _ _), x₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hys : ofBytes ((Spec.Ecdsa.bytesAt s₀.mem (ptr s₀ 2) (1 + 2 * c.C.len)).drop (c.C.len + 1)) =
      sv c (ptr s₀ 3) s₃ QY := by
    rw [peer_bytes, List.drop_succ_cons, List.drop_left' (length_bytesAt _ _ _), y₃,
      bytesAt_keep W₂ (hp.peer_sc.sub_left (Offset.sub_base _ (by omega))) (by omega) (by omega)]
  have hP' : ∀ h : Ecdh.Valid c.C (s₀.mem (ptr s₀ 2)) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY),
      peerPt c (s₀.mem (ptr s₀ 2) = 4) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY) =
        .affine ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩ := fun h => by
    unfold peerPt; rw [dite_eq_left ⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2⟩]
  have hk : sv c (ptr s₀ 3) s₄ K = dk c s₀ := by
    rw [e₄ (by decide) (by decide) (by decide), e₃ (by decide) (by decide) (by decide),
      S₂.k, kv_eq (A := Args.ecdh) rfl]
  have hR := L.q
  rw [hk] at hR
  have hxoX : Fin.ofNat c.C.p xv = tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RX) *
      tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ^ (c.C.p - 2) := by rw [hxv, L.acc]
  have hspec := exchange_eq_of_lt hC hlen hb0 hxs hys hP' hR hxl hxoX
  have hD₅ : sv c (ptr s₀ 3) s₅ D = dk c s₀ := by
    rw [e₅ (by decide) (by decide) (by decide), e₄ (by decide) (by decide) (by decide),
      e₃ (by decide) (by decide) (by decide), S₂.d, dv_eq (A := Args.ecdh) rfl]
  have hz : tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ≠ 0 ↔ sv c (ptr s₀ 3) s₅ RZ ≠ 0 :=
    not_congr (toM_eq_zero_iff hpR L.rz_lt)
  unfold EPost
  rw [hspec]
  by_cases hcond : (1 ≤ dk c s₀ ∧ dk c s₀ < c.C.n) ∧
      Ecdh.Valid c.C (s₀.mem (ptr s₀ 2)) (sv c (ptr s₀ 3) s₃ E) (sv c (ptr s₀ 3) s₃ QY) ∧
      tmv c.C c.n (ptr s₀ 3) s₅ (c.sl RZ) ≠ 0
  · have hok : ok c (ptr s₀ 3) s₅ (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
        sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) = true := by
      refine decide_eq_true ⟨⟨⟨⟨⟨hcond.2.1.1, hcond.2.1.2.1⟩, hcond.2.1.2.2.1⟩, hcond.2.1.2.2.2⟩, ?_, ?_⟩,
        hz.mp hcond.2.2⟩
      · rw [hD₅]; exact hcond.1.1
      · rw [hD₅]; exact hcond.1.2
    rw [ite_eq_left hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩
  · have hok : ok c (ptr s₀ 3) s₅ (PeerOk c (ptr s₀ 3) s₃ ((s₀.mem (ptr s₀ 2) = 4 ∧
        sv c (ptr s₀ 3) s₃ E < c.C.p) ∧ sv c (ptr s₀ 3) s₃ QY < c.C.p)) = false := by
      refine decide_eq_false fun h => hcond ⟨⟨?_, ?_⟩, ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2⟩,
        hz.mpr h.2⟩
      · rw [← hD₅]; exact h.1.2.1
      · rw [← hD₅]; exact h.1.2.2
    rw [ite_eq_right hcond]
    exact ⟨by rw [ret, hok]; rfl, by rw [bytes, hok]; rfl⟩

end VG.Proof.Ecdh.X86
