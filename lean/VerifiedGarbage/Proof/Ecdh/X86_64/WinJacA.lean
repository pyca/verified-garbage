import VerifiedGarbage.Proof.Ecdh.X86_64.WinJac
import VerifiedGarbage.Proof.Ecdh.X86_64.MulJ4
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJacA

/-!
# ECDH on x86-64: `[d]P` by 5-bit windows with an affine table

`Cfg.mulQJA`: `mulQJ` (`WinJac.lean`) with the window method's table made
affine (`JacWinCfg.windowA`, `winJacA_ok`). Its inversion (`Cfg.invJA`,
`invSpecJA`) leaves `R.z^(p-2)` in the selected entry's `X` (`E.x`, a slot of
the grid) and writes the temporary area and the working area of `invWin`,
over the table of the bits of `n - 2`, below the window's table of bits: so
`mulQJA` writes what `mulQJ` writes and that area (`mulQJAW`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The table's inversion -/

theorem invJA_acc (c : Cfg) : (Impl.Ecdh.X86_64.Cfg.invJA c).acc = c.sl (WT + 80) := by
  show c.sl WT + 16 * (40 * c.n) = _
  simp (disch := sl_ne) only [sl_eq]; unfold WT; omega_arith

/-- The working area ends below the window's table of bits. -/
theorem invTbl_below (h4 : 4 ≤ c.n) : bitsAt c.n 2 + invTbl c.n ≤ c.sl WB := by
  rw [bitsAt_eq]; simp (disch := sl_ne) only [sl_eq]; simp only [invTbl]; unfold WB; omega_arith

/-- The inversion of the window method with an affine table: its slots and
working area. -/
theorem invLayJA (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) :
    InvLay (Impl.Ecdh.X86_64.Cfg.invJA c) size := by
  have h7 := hc.n10
  have h4 : 4 ≤ c.n := by omega_arith
  have hT : bitsAt c.n 2 + invTbl c.n ≤ size := by
    have := invTbl_below h4; have := sl_le_jw c h46 (i := WB) (by decide); omega
  have below : ∀ {i}, i < 45 → i ≠ TMP → c.sl i + 8 * c.n ≤ bitsAt c.n 2 := fun hi hT => by
    have := sl_below_bits c hi 2 0 (.inl hT); omega
  have hacc := invJA_acc c
  have above : bitsAt c.n 2 + invTbl c.n ≤ c.sl (WT + 80) := by
    have := invTbl_below h4; have := sl_lt c (show WB < WT + 80 by decide); omega_arith
  refine ⟨h4, show c.n < 10 by omega_arith, ?_, sl_le c h7 (i := RZ) (by decide), hT,
    sl_le c h7 (i := MP) (by decide), sl_le c h7 (i := TMP) (by decide), ?_, ?_,
    Or.inl (below (by decide) (by decide)), ?_,
    (sl_apart_hi c (i := TMP) (by decide) (Nat.le_refl _) invW_below_tmp).symm, ?_,
    Or.inl (below (by decide) (by decide)),
    sl_apart c (by decide)⟩ <;> rw [hacc]
  · exact sl_le_jw c h46 (by decide)
  · exact sl_apart c (by decide)
  · exact Or.inr above
  · exact sl_apart c (by decide)
  · exact sl_apart c (by decide)

/-- The inversion as the window method takes it: `E.x = R.z^(p-2)`, writing
`E.x`, the temporary area and a working area apart from the window's slots and
table of bits. -/
theorem invSpecJA (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) {base : Addr} :
    InvSpecJ (jwQ c) c.C base size (InvCfg.inv (Impl.Ecdh.X86_64.Cfg.invJA c))
      (invW (Impl.Ecdh.X86_64.Cfg.invJA c)) := by
  obtain ⟨h4, sp, ip⟩ := hc.inv (by omega_arith)
  have h7 := hc.n10
  have hJle := jwinJ_le hc
  refine ⟨fun t ht hM hz => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · exact WP.mono (sp (invLayJA hc h46) (by have := hc.p_ge; omega_arith) (unitMod_pow_two hc.p_odd (64 * c.n))
      ht hM hz ⟨ip.B1, ip.B16, ip.C, ip.Cpos, ip.Cn, ip.bound⟩) fun t' ⟨a, b, d, e⟩ => ⟨a, b, d, e⟩
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr (Or.inr ⟨Or.inl (show c.sl MP + 8 * c.n ≤ bitsAt c.n 2 by
        have := sl_below_bits c (i := MP) (by decide) 2 0; omega_arith), fun x hx => ?_⟩)
      rw [jwSlots_eq] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      have key : ∀ i ∈ roJ ++ otherJ ++ gridJ, i < 45 ∨ WT ≤ i := by decide
      rcases key i hi with h | h
      · exact sl_apart_hi c h (Nat.le_refl _) invW_below_tmp
      · refine Or.inr ?_
        show bitsAt c.n 2 + invTbl c.n ≤ c.sl i
        have := invTbl_below h4
        have := sl_lt c (show WB < WT by decide)
        have : c.sl WT ≤ c.sl i := by
          simp (disch := sl_ne) only [sl_eq]; exact Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _
        omega_arith
    · exact Or.inr (Or.inl rfl)
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    have hb : (jwQ c).bits = c.sl WB := rfl
    have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
    rw [hb, hJ]
    rcases hw with rfl | rfl | rfl
    · refine Or.inl ?_
      show c.sl WB + 5 * Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ (Impl.Ecdh.X86_64.Cfg.invJA c).acc
      rw [invJA_acc]; simp (disch := sl_ne) only [sl_eq]; unfold WB WT; omega_arith
    · exact Or.inr (invTbl_below h4)
    · by_cases h6 : c.n = 6
      · refine Or.inl ?_
        show c.sl WB + 5 * Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ c.sl TMP
        rw [sl_tmp6 c h6]; simp (disch := sl_ne) only [sl_eq]; unfold WB
        rw [h6] at hJle ⊢; omega
      · exact Or.inr (sl_lt c (show TMP < WB by decide) (.inr (.inr ⟨h6, by decide⟩)))

/-- What the window method with an affine table writes, inversion included. -/
theorem invJA_w :
    ∀ w ∈ jwW (jwQ c) ++ invW (Impl.Ecdh.X86_64.Cfg.invJA c),
      w ∈ winXJ c ++ slW c (otherJ ++ gridJ ++ [TMP]) := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · rw [jwW_eq] at hw; exact List.mem_append_right _ hw
  · simp only [invW, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨WT + 80, by decide, ?_⟩)
      rw [invJA_acc]; rfl
    · exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _))
    · exact List.mem_append_right _ (List.mem_map.mpr ⟨TMP, by decide, rfl⟩)

/-! ## `[d]P` and `Z^(p-2)` -/

/-- What `mulQJA` and the power may write: what `mulQJ` and the power may, and
the inversion's working area (`winXJ`). -/
abbrev mulQJAW (c : Cfg) : List (Nat × Nat) := winXJ c ++ slW c mulJI ++ pwW c

theorem mulQJA_w (hc : CfgOk c) : MulW c (mulQJAW c) where
  fixed := (fixedOk_winXJ.append (fixedOk_slW mulJI_idx)).append fixedOk_pwW
  d := apart_append (apart_append (apart_winXJ (by decide)) (apart_slW (by decide))) (apart_pwW (by decide) (by decide))
  flag := fun w hw => by
    have := hc.n0
    rcases apart_append (apart_append (apart_winXJ (c := c) (i := FLAG) (by decide))
      (apart_slW (l := mulJI) (by decide))) (apart_pwW (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega_arith)
    · exact Or.inr h

/-- The Jacobian window method with an affine table computes `[d]P` for
`d < n` (`MulOk`), as `mulQJ_ok`. -/
theorem mulQJA_ok (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) (hC : Law c.C) (hO : PrimeOrder c.C)
    {dbl : Pt → Prog isa} (hD : DblOk c.MP' c.rcbSlots c.C dbl) (hn17 : 17 ≤ c.C.n % 32)
    (hn64 : 64 ≤ c.C.n) : MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJA c dbl) (mulQJAW c) := by
  intro base s hs g F hbp P hP hpx hpy hrep _ _ _ k hk hk8 _ ht₁ rest R h
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  have hJle := jwinJ_le hc
  unfold Impl.Ecdh.X86_64.Cfg.mulQJA
  refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
  have F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
  have v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
    sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
  -- `d mod 2^nbits + offset J` and its bits.
  have hk₁ : sv c base s₁ K < 2 ^ c.nbits := by rw [e₁]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hrec : wordsVal s₁.mem base (c.sl K) c.n + JacWinCfg.offset (Impl.Ecdh.X86_64.Cfg.jwinJ c) <
      32 ^ Impl.Ecdh.X86_64.Cfg.jwinJ c := recodeJ_lt hk₁
  have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WK <;> omega_arith
  have hKW := sl_lt c (show K < WK by decide)
  have h32 : (32 : Nat) ^ Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega_arith
  have hBs : c.sl WB + 80 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WB <;> omega_arith
  rw [Impl.Ecdh.X86_64.Cfg.jwinPrep]
  refine WP.seq (WP.seq ?_)
  rw [hK]
  refine WP.mono (addConst_ok hs₁ (n := c.n) (src := c.sl K) (dst := c.sl WK)
    (c := JacWinCfg.offset (Impl.Ecdh.X86_64.Cfg.jwinJ c)) h0 (sl_le c h7 (by decide)) (by omega_arith)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₂ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [e₂] at b₃
  have U₃ : Unch base (winX c) s₁.mem s₃.mem :=
    ((O₂.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₃.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₃ := F₁.unch h7 hn fixedOk_winX U₃
  have e₃ : ∀ {i}, i < 45 → i ≠ K → sv c base s₃ i = sv c base s i := fun hi hne =>
    (sv_unch U₃ h7 hn hi (apart_winX hi)).trans (v₁ hi hne)
  have hM₃ := modP_of hc F₃.mp
  have tv : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₃ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
    fun hi hne => by show toM _ _ (sv c base s₃ _) = toM _ _ (sv c base s _); rw [e₃ hi hne]
  have hF : JacWinFixed (jwQ c) c.C base s₃ P (sv c base s₁ K) := by
    refine ⟨F₃.zero, fun x hx => ?_, ?_, ?_, fun t ht => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact lt_of_eq_of_lt (e₃ (i := PX) (by decide) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₃ (i := PY) (by decide) (by decide)) hpy
      · exact lt_of_eq_of_lt F₃.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₃ (c.sl PX)) (tmv c.C c.n base s₃ (c.sl PY))
        (tmv c.C c.n base s₃ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl ONEP) c.n) = 1
      rw [F₃.onep, show 2 ^ (64 * c.n) % c.C.p = c.mont 1 by simp [Cfg.mont, Cfg.R], toM_cmont hc]; rfl
    · rw [hJ] at ht
      exact b₃ t (by omega_arith)
  refine WP.mono (winJacA_ok (jwLayQ hc h46) hpR hC hc.am3 hO hD hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hn17 hn64 hP
    (by rw [hJ]; exact hrec) (invSpecJA hc h46) hs₃ hM₃ hF) fun s₄ ⟨K₄, U₄', M₄, L₄, R₄⟩ => ?_
  have U₄ : Unch base (winXJ c ++ slW c (otherJ ++ gridJ ++ [TMP])) s₃.mem s₄.mem :=
    U₄'.mono fun w hw => invJA_w w hw
  have hs₄ := hs₃.of_keepRegs K₄ (rdi_not_invClob _)
  have F₄ := F₃.unch h7 hn (fixedOk_winXJ.append (fixedOk_slW (by decide))) U₄
  have rz₄ : wordsVal s₄.mem base (c.sl RZ) c.n < c.C.p :=
    L₄ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc hs₄ M₄ rz₄ F₄.onep (fun h9 t ht => by
      rw [tbl_unch U₄ h7 hn (j := 1) (by decide) ht (apart_append (tbl_apart_winXJ (by decide) ht)
          (tbl_apart_slW' (by decide) (by decide) ht)),
        tbl_unch U₃ h7 hn (j := 1) (by decide) ht (tbl_apart_winX (by decide) ht),
        tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
      exact ht₁ h9 t ht)) fun s₅ ⟨K₅, U₅, lt₅, v₅⟩ => h s₅ ?_)
  have r₅ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₅ i = sv c base s₄ i := fun hi h₁ =>
    sv_unch U₅ h7 hn hi (apart_pwW hi h₁)
  have c₂ : ∀ r ∈ [Reg.rax, .r8], r ∈ invClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [invClob, powClob, clob]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))
  have c₃ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ invClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [invClob, powClob, clob]
  have c₁ : ∀ r ∈ [Reg.r8], r ∈ invClob c.n := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))
  have KK : KeepRegs (invClob c.n) s s₄ :=
    (((k₁.mono c₁).trans (k₂.mono c₂)).trans (k₃.mono c₃)).trans K₄
  refine ⟨hs₄.of_keepRegs K₅ (rdi_not_invClob _), by
      rw [K₅.gpr _ (rsi_not_invClob _), KK.gpr _ (rsi_not_invClob _)], by rw [K₅.rd, KK.rd],
    by rw [K₅.wr, KK.wr], ((U₁.trans U₃).trans (U₄.trans U₅)).mono ?_, fun _ hlt => ?_, lt₅, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
      · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hw))
    · rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_append.mp hw with hw | hw
        · exact List.mem_append_left _ (List.mem_append_left _ hw)
        · exact List.mem_append_left _ (List.mem_append_right _
            (slW_mono (l' := mulJI) (fun _ hi => List.mem_append_left _ hi) hw))
      · exact List.mem_append_right _ hw
  · show Rep _ (toM _ _ (sv c base s₅ RX)) (toM _ _ (sv c base s₅ RY)) (toM _ _ (sv c base s₅ RZ)) _
    rw [r₅ (i := RX) (by decide) (by decide), r₅ (i := RY) (by decide) (by decide),
      r₅ (i := RZ) (by decide) (by decide)]
    have hq := R₄ (by rw [e₁, hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hc.n_bits)]; exact hlt)
    rw [e₁, hk, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hlt hc.n_bits)] at hq
    exact hq
  · show _ = toM _ _ (sv c base s₅ RZ) ^ _
    rw [r₅ (i := RZ) (by decide) (by decide)]
    exact v₅
  · rw [r₅ (i := RZ) (by decide) (by decide)]; exact rz₄

end VG.Proof.Ecdh.X86_64
