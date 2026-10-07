import VerifiedGarbage.Proof.Ecdsa.Verify.X86.WindowLayout

/-! # The x86 P-256 variable-base product -/

namespace VG.Proof.Ecdsa.Verify.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86 VG.Impl.Ecdsa.Verify.X86
open VG.Impl.Ecdh.X86 (PX PY)
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass
open VG.Proof.Ecdsa.X86 Spec.Weierstrass
variable {c : Impl.Ecdsa.X86.Cfg}

/-- Multiply the validated peer by `v`, preserving the fixed-base result. -/
theorem windowMulQ_ok (hc : CfgOk c) (h4 : c.n = 4) (hC : Law c.C) (hM3 : AM3 c.C)
    {s : State} {base : Addr} {g : Reg → BitVec 32} (hs : Scr s base size) (F : Fixed c base g s.mem)
    {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hQ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) :
    WP isa (Impl.Ecdsa.Verify.X86.Cfg.windowMulQ c) s fun u =>
      Keeps powClob s u ∧ Unch base (windowW c) s.mem u.mem ∧
      ModOkW c.MP' size c.C.p u.mem base ∧
      (∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal u.mem base x c.n < c.C.p) ∧
      Rep c.C (tmv c.C c.n base u (c.sl RX)) (tmv c.C c.n base u (c.sl RY))
        (tmv c.C c.n base u (c.sl RZ)) (mul (sv c base s V) P) := by
  have hn := hs.nowrap
  have hp := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  unfold Impl.Ecdsa.Verify.X86.Cfg.windowMulQ
  refine WP.seq (WP.mono (setConst_ok hs (sl_le c hc.n10 (i := EM) (by decide))
    (Nat.lt_trans (hmont _) hc.p_lt)) fun s₁ ⟨v₁, k₁, O₁⟩ => ?_)
  change sv c base s₁ EM = c.mont c.C.b at v₁
  have hs₁ := hs.of_keeps k₁ (by decide)
  have U₁ : Unch base (slW c [EM]) s.mem s₁.mem := O₁.unch
  have F₁ := F.unch hc.n10 hn (fixedOk_slW (by decide)) U₁
  have e₁ : ∀ {i}, i < 45 → i ≠ EM → sv c base s₁ i = sv c base s i :=
    fun hi he => sv_unch U₁ hc.n10 hn hi (apart_slW (by simpa only [List.mem_singleton] using he))
  refine WP.seq (WP.mono (windowPrep_ok h4 hs₁) fun s₂ ⟨bits, k₂, O₂⟩ => ?_)
  have hs₂ := hs₁.of_keeps k₂ (by decide)
  have U₂ := O₂.unch
  have ap₂ : ∀ {i}, i < 45 → ∀ w ∈ [(3520, 500)],
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
    intro i hi w hw
    rw [List.mem_singleton.mp hw]
    left; rw [sl_eq, h4]; omega
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s₁ i :=
    fun hi => sv_unch U₂ hc.n10 hn hi (ap₂ hi)
  have F₂ := F₁.unch hc.n10 hn (show FixedOk c [(3520, 500)] from by
    intro w hw; rw [List.mem_singleton.mp hw]; right; rw [sl_eq, h4]; decide) U₂
  have tv : ∀ {i}, i < 45 → i ≠ EM → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := by
    intro i hi he
    change toM _ _ (sv c base s₂ i) = toM _ _ (sv c base s i)
    rw [e₂ hi, e₁ hi he]
  have hF : WinFixed (Impl.Ecdsa.Verify.X86.Cfg.windowQ c) c.C base s₂ P
      (sv c base s V + WinCfg.offset 65) := by
    refine ⟨?_, ?_, ?_, F₂.zero, ?_, ?_⟩
    · change toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₂.mem base (c.sl AP) c.n) = _
      rw [F₂.ap]; exact toM_cmont hc _
    · change toM c.C.p (2 ^ (64 * c.n)) (sv c base s₂ EM) = _
      rw [e₂ (by decide), v₁]; exact toM_cmont hc _
    · intro x hx
      change x ∈ [c.sl AP, c.sl EM, c.sl ZERO, c.sl PX, c.sl PY, c.sl ONEP] at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact F₂.ap ▸ hmont _
      · change sv c base s₂ EM < _
        rw [e₂ (by decide), v₁]; exact hmont _
      · change wordsVal s₂.mem base (c.sl ZERO) c.n < _
        rw [F₂.zero]; omega
      · change sv c base s₂ PX < _
        rw [e₂ (by decide), e₁ (by decide) (by decide)]; exact hpx
      · change sv c base s₂ PY < _
        rw [e₂ (by decide), e₁ (by decide) (by decide)]; exact hpy
      · change wordsVal s₂.mem base (c.sl ONEP) c.n < _
        rw [F₂.onep]; exact Nat.mod_lt _ (by omega)
    · change Rep c.C (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]
      exact hQ
    · intro t ht
      change s₂.mem (off base (3700 + t)) = _
      rw [bits t ht, e₁ (by decide) (by decide)]
  have hoff : WinCfg.offset 65 = 8 * geom 65 := by decide +kernel
  have hklt : sv c base s V + WinCfg.offset 65 < 16 ^ 65 := by
    have hv : sv c base s V < 2 ^ 256 := by
      change wordsVal s.mem base (c.sl V) c.n < _
      rw [h4]; exact wordsVal_lt _ _ _ 4
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_right hv _) (by decide +kernel)
  refine WP.mono (window_ok (windowLay h4) (windowWk h4)
    (unitMod_pow_two hc.p_odd _) hC hM3 hP hc.p_lt (hmont 1)
    (by change toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1; rw [toM_cmont hc]; rfl)
    hs₂ (modP_of hc F₂.mp) hF hklt (by change 8 * geom 65 ≤ _; rw [← hoff]; omega))
    fun u ⟨ku, Uu, Mu, Lu, qu⟩ => ?_
  have UW₁ : Unch base (windowW c) s.mem s₁.mem := U₁.mono (by
    intro w hw; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact List.mem_append_left _ (List.mem_map.mpr ⟨i, by rw [List.mem_singleton.mp hi]; decide, rfl⟩))
  have UW₂ : Unch base (windowW c) s₁.mem s₂.mem := U₂.cover (by
    intro w hw; rw [List.mem_singleton.mp hw]
    exact ⟨(2640, 1500), List.mem_append_right _ (List.mem_singleton_self _), by decide, by decide⟩)
  refine ⟨((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans ku,
    fun x hx => (Uu.cover (windowW_cover h4) x hx).trans ((UW₂ x hx).trans (UW₁ x hx)), Mu, Lu, ?_⟩
  change Rep _ _ _ _ (mul (sv c base s V + WinCfg.offset 65 - 8 * geom 65) P) at qu
  rw [hoff, Nat.add_sub_cancel] at qu
  exact qu
end VG.Proof.Ecdsa.Verify.X86
