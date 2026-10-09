import VerifiedGarbage.Proof.Ecdsa.Verify.AArch64.P192.Sum
import VerifiedGarbage.Proof.Ecdh.AArch64.P192.Mul

/-! # p192 verification: two complete ladders and their sum -/

namespace VG.Proof.Ecdsa.Verify.AArch64.P192

open VG VG.AArch64 VG.Impl.Ecdsa.AArch64 VG.Impl.Weierstrass VG.Impl.Weierstrass.AArch64
open VG.Impl.Ecdh.AArch64 (PX PY)
open VG.Impl.Ecdsa.Verify.AArch64 (U V UX UY UZ RM')
open VG.Proof.Ecdsa.AArch64 VG.Proof.Ecdsa.AArch64.P192
open VG.Proof.Mont VG.Proof.Mont.AArch64 VG.Proof.Weierstrass VG.Proof.Weierstrass.AArch64
open Spec.Weierstrass

abbrev ptsW : List Nat := [EXPP, RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TX, TY, TZ,
  TMP, UX, UY, UZ]

theorem points_ok (hc : BaseCfgOk p192) {s₀ : State} {base : Addr} {g : Reg → BitVec 64} {s : State}
    (hM : Mid p192 s₀ base g s) {Q₁ Q₂ : Nat → Fe p192.C → Fe p192.C → Fe p192.C → Prop}
    (hC : Law p192.C)
    (hQ₁ : ∀ X Y Z, Rep p192.C X Y Z (mul (sv p192 base s U) (G p192.C)) → Q₁ 0 X Y Z)
    {P : Point p192.C} (hP : onCurve p192.C P = true)
    (hrep : Rep p192.C (tmv p192.C p192.n base s (p192.sl PX)) (tmv p192.C p192.n base s (p192.sl PY))
      (tmv p192.C p192.n base s (p192.sl ONEP)) P)
    (hQ₂ : ∀ X Y Z, Rep p192.C X Y Z (mul (sv p192 base s V) P) → Q₂ 0 X Y Z)
    {rest : Prog isa} {Q : State → Prop}
    (h : ∀ s', Pts p192 s₀ base g Q₁ Q₂ s' → WP isa rest s' Q) :
    WP isa (.seq (Impl.Ecdsa.Verify.AArch64.P192.points) rest) s Q := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hM.scr.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * p192.n)
  have hp3 := hc.p_ge
  have F := hM.fixed
  have hmont : ∀ x, p192.mont x < p192.C.p := fun x => Nat.mod_lt _ (by omega)
  have tb : ∀ {i}, i < 45 → ∀ w ∈ [(bitsAt p192.n 0, 64 * p192.n)], p192.sl i + 8 * p192.n ≤ w.1 ∨ w.1 + w.2 ≤ p192.sl i :=
    fun hi => apart_tbl hi 0 h7
  unfold Impl.Ecdsa.Verify.AArch64.P192.points
  refine WP.seq ?_
  -- The table of `u`.
  refine WP.seq (WP.mono_syms (bits_ok hM.scr h0 (by omega) (sl_le p192 h7 (i := U) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := U) (by decide)) (by have := bitsAt0_le p192 h7; omega) (Or.inl (by have := sl_below_bits p192 (i := U) (by decide) 0 0; omega)))
    fun s₁ ⟨b₁, k₁, O₁⟩ sy₁ => ?_)
  have hs₁ := hM.scr.of_keepRegs k₁ (by decide)
  have U₁ : Unch base [(bitsAt p192.n 0, 64 * p192.n)] s.mem s₁.mem := O₁.unch
  have F₁ := F.unch h7 hn (fixedOk_tbl 0) U₁
  have v₁ : ∀ {i}, i < 45 → sv p192 base s₁ i = sv p192 base s i := fun hi => sv_unch U₁ h7 hn hi (tb hi)
  -- `[u]G` by the complete ladder.
  have WC := Ecdsa.AArch64.P192.gMul_ok hc hC hs₁ F₁ (wordsVal_lt _ _ _ _)
    (by rw [v₁ (by decide)]; exact hM.rx)
    (by rw [v₁ (by decide)]; exact hM.ry)
    (by rw [v₁ (by decide)]; exact hM.rz) b₁
  refine WP.seq (WP.mono WC fun s₂ ⟨K₂, U₂, M₂, L₂, R₂⟩ => ?_)
  have q₂ := hQ₁ _ _ _ R₂
  have F₂ := F₁.unch h7 hn (fixedOk_slW (l := gSlots) (by decide)) U₂
  have hs₂ := hs₁.of_keepRegs K₂ (x0_not_powClob h7)
  refine WP.seq (WP.mono (save_ok hc hs₂) fun s₃ ⟨hs₃, k₃, U₃, ux₃, uy₃, uz₃, rx₃, ry₃, rz₃⟩ => ?_)
  have F₃ := F₂.unch h7 hn (fixedOk_slW (by decide)) U₃
  have sub₂ : ∀ i ∈ gSlots, i ∈ ptsW := by decide
  have sub₃ : ∀ i ∈ saveW, i ∈ ptsW := by decide
  have W₃ : ∀ {i}, i < 45 → i ∉ ptsW → sv p192 base s₃ i = sv p192 base s i := fun hi hl =>
    ((sv_unch U₃ h7 hn hi (apart_slW (fun h => hl (sub₃ _ h)))).trans
      (sv_unch U₂ h7 hn hi (apart_slW (fun h => hl (sub₂ _ h))))).trans (v₁ hi)
  -- The bits of `v`, retaining the saved first point and peer.
  refine WP.seq (WP.mono (bits_ok hs₃ h0 (by omega) (sl_le p192 h7 (i := V) (by decide))
    (tbl_le h7) (sl_lt4096 h0 h7 (i := V) (by decide)) (by have := bitsAt0_le p192 h7; omega)
    (Or.inl (by have := sl_below_bits p192 (i := V) (by decide) 0 0; omega)))
    fun s₄ ⟨b₄, k₄, O₄⟩ => ?_)
  have U₄ : Unch base [(bitsAt p192.n 0, 64 * p192.n)] s₃.mem s₄.mem := O₄.unch
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  have F₄ := F₃.unch h7 hn (fixedOk_tbl 0) U₄
  have v₄ : ∀ {i}, i < 45 → sv p192 base s₄ i = sv p192 base s₃ i := fun hi => sv_unch U₄ h7 hn hi (tb hi)
  have tv₄ : ∀ {i}, i < 45 → i ∉ ptsW → tmv p192.C p192.n base s₄ (p192.sl i) = tmv p192.C p192.n base s (p192.sl i) :=
    fun hi hl => by
      show toM _ _ (sv p192 base s₄ _) = toM _ _ (sv p192 base s _)
      rw [v₄ hi, W₃ hi hl]
  refine WP.seq (WP.mono (Ecdh.AArch64.P192.qMul_ok hc hC hP hs₄ F₄
    (by rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.px_lt)
    (by rw [v₄ (by decide), W₃ (by decide) (by decide)]; exact hM.py_lt)
    (by
      change Rep p192.C (tmv p192.C p192.n base s₄ (p192.sl PX))
        (tmv p192.C p192.n base s₄ (p192.sl PY))
        (tmv p192.C p192.n base s₄ (p192.sl ONEP)) P
      rw [tv₄ (by decide) (by decide), tv₄ (by decide) (by decide), tv₄ (by decide) (by decide)]
      exact hrep)
    (k := sv p192 base s V) (wordsVal_lt _ _ _ _)
    (by rw [v₄ (by decide)]; exact rx₃) (by rw [v₄ (by decide)]; exact ry₃)
    (by rw [v₄ (by decide)]; exact rz₃)
    (fun t ht => by
      rw [b₄ t ht]
      change (if (sv p192 base s₃ V).testBit t then 1 else 0) = _
      rw [W₃ (i := V) (by decide) (by decide)]))
    fun s₅ ⟨K₅, U₅, M₅, L₅, R₅, B₅⟩ => ?_)
  have hs₅ := hs₄.of_keepRegs K₅ (x0_not_powClob h7)
  have F₅ := F₄.unch h7 hn (fixedOk_slW (l := gSlots) (by decide)) U₅
  have v₅ : ∀ {i}, i < 45 → i ∉ ptsW → sv p192 base s₅ i = sv p192 base s₃ i := fun hi hl =>
    (sv_unch U₅ h7 hn hi (apart_slW (fun h => hl (sub₂ _ h)))).trans (v₄ hi)
  have q₅ := hQ₂ _ _ _ R₅
  have u₅ : ∀ {i}, i ∈ [UX, UY, UZ] → sv p192 base s₅ i = sv p192 base s₃ i := fun {i} hi => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      exact (sv_unch U₅ h7 hn (by decide) (apart_slW (by decide))).trans (v₄ (by decide))
  refine WP.mono (sum_ok hc hs₅ M₅ (fun i hi => ?_)) fun s₆ ⟨hs₆, rd₆, wr₆, U₆, M₆, rz₆, t₆⟩ => h s₆ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · change wordsVal s₅.mem base (p192.sl AP) p192.n < _
      rw [F₅.ap]; exact hmont _
    · rw [B₅]; exact hmont _
    · rw [u₅ (by decide), ux₃]; exact L₂ _ (by simp)
    · rw [u₅ (by decide), uy₃]; exact L₂ _ (by simp)
    · rw [u₅ (by decide), uz₃]; exact L₂ _ (by simp)
    · exact L₅ _ (by simp)
    · exact L₅ _ (by simp)
    · exact L₅ _ (by simp)
  have F₆ := F₅.unch h7 hn (fixedOk_slW (by decide)) U₆
  have sub₆ : ∀ i ∈ sumW, i ∈ ptsW := by decide
  have v₆ : ∀ {i}, i < 45 → i ∉ ptsW → sv p192 base s₆ i = sv p192 base s i := fun hi hl =>
    (sv_unch U₆ h7 hn hi (apart_slW (fun h => hl (sub₆ _ h)))).trans ((v₅ hi hl).trans (W₃ hi hl))
  have UW : Unch base ([(bitsAt p192.n 0, 64 * p192.n)] ++ slW p192 ptsW) s.mem s₆.mem := by
    refine (U₁.trans (U₂.trans (U₃.trans (U₄.trans (U₅.trans U₆))))).mono fun w hw => ?_
    simp only [List.mem_append] at hw ⊢
    rcases hw with hw | hw | hw | hw | hw | hw
    · exact .inl hw
    · exact .inr (List.map_subset _ sub₂ hw)
    · exact .inr (List.map_subset _ sub₃ hw)
    · exact .inl hw
    · exact .inr (List.map_subset _ sub₂ hw)
    · exact .inr (List.map_subset _ sub₆ hw)
  have tu : ∀ {i j}, i ∈ [UX, UY, UZ] → j ∈ [RX, RY, RZ] → sv p192 base s₃ i = sv p192 base s₂ j →
      tmv p192.C p192.n base s₅ (p192.sl i) = tmv p192.C p192.n base s₂ (p192.sl j) := fun hi _ e => by
    show toM _ _ (sv p192 base s₅ _) = toM _ _ (sv p192 base s₂ _)
    rw [u₅ hi, e]
  have ha : tmv p192.C p192.n base s₅ (p192.sl AP) = Fin.ofNat p192.C.p p192.C.a := by
    show toM _ _ (wordsVal s₅.mem base (p192.sl AP) p192.n) = _
    rw [F₅.ap]; exact toM_cmont hc _
  have hb : tmv p192.C p192.n base s₅ (p192.sl EXPP) = Fin.ofNat p192.C.p (3 * p192.C.b) := by
    show toM _ _ (sv p192 base s₅ EXPP) = _
    rw [B₅]; exact toM_cmont hc _
  refine ⟨hs₆, by rw [wr₆, K₅.wr, k₄.wr, k₃.wr, K₂.wr, k₁.wr, hM.wr],
    by rw [rd₆, K₅.rd, k₄.rd, k₃.rd, K₂.rd, k₁.rd, hM.rd], F₆, ?_,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm_lt,
    by rw [v₆ (by decide) (by decide)]; exact hM.rm, rz₆.1,
    ⟨_, _, _, _, _, _, q₂, q₅, by
      rw [t₆, ha, hb, tu (by decide) (by decide) ux₃,
        tu (by decide) (by decide) uy₃, tu (by decide) (by decide) uz₃]
      rfl⟩,
    ?_, by rw [v₆ (by decide) (by decide)]; exact hM.k, rz₆.2⟩
  · rw [UW.word (fun w hw => ?_) (by have := sl_le p192 h7 (i := FLAG) (by decide); omega)]
    · exact hM.flag
    · rcases List.mem_append.mp hw with hw | hw
      · rw [List.mem_singleton.mp hw]
        have := sl_below_bits p192 (i := FLAG) (by decide) 0 0
        exact .inl (by dsimp only; omega)
      · exact (apart_slW (c := p192) (i := FLAG) (l := ptsW) (by decide)) w hw |>.elim
          (fun h => Or.inl (by omega)) (fun h => Or.inr h)
  · refine unch_whole (hM.unch.trans UW) fun w hw => ?_
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact Nat.le_refl _
    rcases List.mem_append.mp hw with hw | hw
    · rw [List.mem_singleton.mp hw]; exact tbl_le h7
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      exact sl_le p192 h7 ((show ∀ i ∈ ptsW, i < 45 by decide) i hi)

end VG.Proof.Ecdsa.Verify.AArch64.P192
