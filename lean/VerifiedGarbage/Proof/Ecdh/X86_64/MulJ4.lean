import VerifiedGarbage.Proof.Ecdh.X86_64.MulOk
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJLoop

/-!
# ECDH on x86-64: `[d]P` by 4-bit windows with a Jacobian accumulator

`Cfg.mulQJ4`, for a curve of prime order whose order `n` is above the
multiples of every iteration but the last (`winE_two_bound`): `winMulJ_ok`
recodes `d` and runs `WinCfg.windowJ` (`windowJ_ok`), as `winMul_ok` runs
the window method, and `mulQJ4_ok` is it with `d` reduced first and the
power after it, as `mulPow_ok`'s windows. It writes what `mulQ` writes
(`mulQW`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-- `winMul_ok` by windows in Jacobian coordinates (`windowJ_ok`), for a curve
of prime order (`PrimeOrder`), with the bound it needs for scalars
of `nbits` bits. -/
theorem winMulJ_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {ks : Nat} (hks : ks < 45)
    (hk8 : sv c base s ks < 2 ^ c.nbits) {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinMulPost c base P (sv c base s ks) s s' → WP isa rest s' R) :
    WP isa (.seq (.seq (c.winPrep (c.sl ks)) (WinCfg.windowJ (winQ c))) rest) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hrec : wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ < 16 ^ c.winJ := recode_lt_bits hk8
  have hJle : c.winJ ≤ 16 * c.n + 1 := by
    unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WK + 1) (by decide)
    rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
  have hKW := sl_lt c (show ks < WK by unfold WK; omega)
  have h16 : (16 : Nat) ^ c.winJ ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : (winQ c).J = c.winJ := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e82 : c.sl WK + 16 * c.n = c.sl WB := by rw [sl_eq, sl_eq]; unfold WK WB; omega
  have h4 := (hc.inv (by omega)).1
  have hB8 : c.sl WB + 64 * (c.n + 1) ≤ c.sl WB + 80 * c.n := by omega
  have hBs : c.sl WB + 80 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WB + 9) (by decide)
    rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
  rw [Cfg.winPrep]
  refine WP.seq (WP.seq (WP.seq ?_))
  rw [hK, offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl ks) (dst := c.sl WK)
    (c := 8 * geom c.winJ) h0 (sl_le c h7 hks) (by omega)
    (Or.inl (by omega)) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega) (by omega)
    (by omega) (by omega) (Or.inl (by omega))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hF : WinFixed (winQ c) c.C base s₂ P (wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₂.zero, ?_, fun t ht => ?_⟩
    · show toM _ _ (wordsVal s₂.mem _ (c.sl AP) c.n) = _; rw [F₂.ap]; exact toM_cmont hc _
    · show toM _ _ (sv c base s₂ BP) = _; rw [e₂ (by decide), hbp]; exact toM_cmont hc _
    · simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₂.ap (hmont _)
      · exact lt_of_eq_of_lt ((e₂ (i := BP) (by decide)).trans hbp) (hmont _)
      · exact lt_of_eq_of_lt F₂.zero (by omega)
      · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide)) hpy
      · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
    · show Rep _ (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide), tv (by decide), tv (by decide)]; exact hrep
    · rw [hJ] at ht
      exact b₂ t (by omega)
  have hJ2 : 2 ≤ c.winJ := by
    unfold Cfg.winJ
    have hnb := hc.n_bits
    by_contra hlt
    have : 2 ^ c.nbits ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hP0 : P ≠ .infinity := by
    intro e
    have hz := (hrep.z_eq_zero_iff).mpr e
    have h1 : tmv c.C c.n base s (c.sl ONEP) = 1 := by
      show toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = 1
      rw [F.onep]; exact toM_one hpR
    exact hC.one_ne_zero (h1 ▸ hz)
  refine WP.mono (windowJ_ok (winLayQ hc h9) (winXQ hc h9) hpR hC hc.am3 hO hP hP0 hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hs₂ hM₂ hF
    (by rw [hJ]; exact hrec) (Nat.le_add_left _ _) (by rw [hJ]; exact hJ2)
    (by rw [hJ]; exact winE_two_bound hJ2 hk8 hbd)) fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => h s₃ ?_
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  have c₁ : ∀ r ∈ [Reg.rax, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  have c₂ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  exact ⟨hs₂.of_keepRegs K₃ (rdi_not_powClob _), ((k₁.mono c₁).trans (k₂.mono c₂)).trans K₃,
    U₂.trans U₃, M₃, L₃, R₃⟩

/-- `mulPow_ok` for `mulQJ4`. -/
theorem mulPowJ4_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {k : Nat} (hk : sv c base s K = k) (hk8 : k < 2 ^ (8 * c.C.len))
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', MulPost c base P k s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdh.X86_64.Cfg.mulQJ4 c) (.seq c.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Impl.Ecdh.X86_64.Cfg.mulQJ4
  · refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
    have F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
    have v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
      sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
    have tv₁ : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
      fun hi hne => by show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _); rw [v₁ hi hne]
    refine WP.seq_iff.mp (winMulJ_ok hc h9 hC hO hbd hs₁ F₁ (by rw [v₁ (by decide) (by decide)]; exact hbp) hP
      (by rw [v₁ (by decide) (by decide)]; exact hpx) (by rw [v₁ (by decide) (by decide)]; exact hpy)
      (by rw [tv₁ (by decide) (by decide), tv₁ (by decide) (by decide), tv₁ (by decide) (by decide)]; exact hrep)
      (ks := K) (by decide) (by rw [e₁]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))) fun s₃ W => ?_)
    have F₃ := F₁.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
    have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := W.lt _ (by simp)
    refine WP.seq (WP.mono (pPow_ok hc W.scr W.mod rz₃ F₃.onep (fun t ht => by
        rw [tbl_unch W.unch h7 hn (j := 1) (by decide) ht (apart_append (tbl_apart_winX (by decide) ht)
          (tbl_apart_slW' (by decide) (by decide) ht)),
          tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
        exact ht₁ t ht)) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
    have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
      sv_unch U₄ h7 hn hi (apart_pwW hi h₁)
    refine ⟨W.scr.of_keepRegs K₄ (rdi_not_invClob _), fun r hr => ?_, by rw [K₄.rd, W.keep.rd, k₁.rd],
      by rw [K₄.wr, W.keep.wr, k₁.wr], ((U₁.trans W.unch).trans U₄).mono ?_, fun hlt => ?_, lt₄, ?_, ?_⟩
    · rw [K₄.gpr r hr, W.keep.gpr r (fun h => hr (List.mem_cons_of_mem _ h)),
        k₁.gpr r (fun h => hr (by
          rw [List.mem_singleton.mp h]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))))]
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
        · rcases List.mem_append.mp hw with hw | hw
          · exact List.mem_append_left _ (List.mem_append_left _ hw)
          · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
      · exact List.mem_append_right _ hw
    · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
      rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
        r₄ (i := RZ) (by decide) (by decide)]
      have hq := W.q
      rw [e₁, hk, Nat.mod_eq_of_lt hlt] at hq
      exact hq
    · show _ = toM _ _ (sv c base s₄ RZ) ^ _
      rw [r₄ (i := RZ) (by decide) (by decide)]
      exact v₄
    · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

theorem mulQJ4_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) (hO : PrimeOrder c.C)
    (hbd : 16 * ((2 ^ c.nbits + 135) / 256) + 8 < c.C.n) :
    MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJ4 c) (mulQW c) :=
  fun hs _ F hbp _ hP hpx hpy hrep _ _ _ _ hk hk8 _ ht₁ _ _ h =>
    mulPowJ4_ok hc h9 hC hO hbd hs F hbp hP hpx hpy hrep hk hk8 ht₁ fun s' L =>
      h s' ⟨L.scr, L.gpr _ (rsi_not_invClob _), L.rd, L.wr, L.unch,
        fun _ hn => L.q (Nat.lt_of_lt_of_le hn hc.n_bits), L.acc_lt, L.acc, L.rz_lt⟩

end VG.Proof.Ecdh.X86_64
