import VerifiedGarbage.Proof.Ecdh.X86_64.MulOk
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinJac

/-!
# ECDH on x86-64: `[d]P` by 5-bit windows in Jacobian coordinates

For four or six words and a curve of prime order `n` with `n mod 32 ≥ 17`
(P-256, P-384), the Jacobian window method (`Cfg.mulQJ`): its slots are numbered slots, its grid
of 85 (the table of 16 entries of five coordinates, then the selected entry)
slots `WT … WT + 84` past the tables of bits (`jwSlots_eq`), so they are apart
as `winJac_ok` needs (`jwLayQ`). `mulQJ_ok`: `d` reduced below `2^nbits`
(`maskK`), recoded into `d + 16 Σ_{j<J} 32^j` and its bits (`jwinPrep`), the
window method on the peer's point (or `G`), then the signature's power: `R`
represents `[d]P` for `d < n` (`MulOk`), with any doubling that doubles a
Jacobian triple in place (`DblOk`). It writes only `mulQJW` (`mulQJ_w`).
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The slots -/

/-- The Jacobian window method's configuration for ECDH. -/
abbrev jwQ (c : Cfg) : JacWinCfg := Impl.Ecdh.X86_64.Cfg.jwinCfg c

/-- The indices of its slots: read only, written, and the grid. -/
def roJ : List Nat := [AP, B3P, ZERO, PX, PY, ONEP]
def otherJ : List Nat := [RX, RY, RZ, DX, DY, DZ, PT, T0, T1, T2, T3, T4, T5]
def gridJ : List Nat := (List.range 85).map (WT + ·)

theorem jwGrid_eq (c : Cfg) : jwGrid (jwQ c) = gridJ.map c.sl := by
  simp only [jwGrid, gridJ, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show c.sl WT + 8 * c.n * i = c.sl (WT + i)
  simp (disch := sl_ne) only [sl_eq]; rw [Nat.mul_add, Nat.add_assoc]

theorem jwSlots_eq (c : Cfg) : jwSlots (jwQ c) = (roJ ++ otherJ ++ gridJ).map c.sl := by
  rw [jwSlots, jwGrid_eq, List.map_append, List.map_append]; rfl

theorem jwW_eq (c : Cfg) : jwW (jwQ c) = slW c (otherJ ++ gridJ ++ [TMP]) := by
  rw [jwW, jwWs, jwGrid_eq]; simp only [slW, List.map_append, List.map_map]; rfl

theorem jwIdx_lt : ∀ i ∈ roJ ++ otherJ ++ gridJ, i < 168 ∧ i ≠ MP ∧ i ≠ TMP := by decide

/-- Every slot below `168` is in the working space, for four or six words. -/
theorem sl_le_jw (c : Cfg) (h46 : c.n = 4 ∨ c.n = 6) {i : Nat} (hi : i < 168) : c.sl i + 8 * c.n ≤ size := by
  simp only [sl_eq', ix, show ¬ c.n = 9 by omega, ↓reduceIte]
  rcases h46 with h4 | h4 <;> rw [h4] <;> show _ ≤ 8192 <;> omega

theorem lay_jw (h46 : c.n = 4 ∨ c.n = 6) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 168 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le_jw c h46 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem jwinJ_le (hc : CfgOk c) : Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 13 * c.n + 1 := by
  unfold Impl.Ecdh.X86_64.Cfg.jwinJ; have := hc.len_hi; have := hc.nbits_le; omega

theorem jwLayQ (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) : JacWinLay (jwQ c) size := by
  have hn := hc.n0
  have hJ : (jwQ c).J = Impl.Ecdh.X86_64.Cfg.jwinJ c := rfl
  have hJle := jwinJ_le hc
  have hJ2 : 2 ≤ Impl.Ecdh.X86_64.Cfg.jwinJ c := by
    unfold Impl.Ecdh.X86_64.Cfg.jwinJ
    have := hc.len8
    by_cases h : c.nbits < 8 * c.C.len
    · have := (hc.mask h).1; omega
    · omega
  have hb : (jwQ c).bits = c.sl WB := rfl
  have hK : (jwQ c).tbl = c.sl WT := rfl
  have hMn : (jwQ c).M.n = c.n := rfl
  refine ⟨h46, ?_, ?_, ?_, ?_, rfl, ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [jwSlots_eq]; exact lay_jw h46 rfl rfl rfl jwIdx_lt
  · exact map_sl_disj hn (l₁ := roJ) (l₂ := otherJ) (by decide)
  · exact map_sl_nodup hn (l := otherJ) (by decide)
  · intro x hx
    have hx' : x ∈ (roJ ++ otherJ).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    have key : ∀ i ∈ roJ ++ otherJ, i < WT := by decide
    rw [hK, hMn]; exact Or.inl (sl_lt c (key i hi))
  · rw [hK]; simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WT <;> omega
  · rw [hb, hJ]; simp (disch := sl_ne) only [sl_eq]
    rcases h46 with h4 | h4 <;> rw [h4] <;> show _ ≤ 8192 <;> unfold WB <;> omega
  · intro w hw
    rw [jwW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hb, hJ]
    have key : ∀ i ∈ otherJ ++ gridJ ++ [TMP], i < WB ∨ WT ≤ i := by decide
    rcases key i hi with h | h
    · exact Or.inr (sl_lt c h)
    · refine Or.inl ?_
      dsimp only
      simp (disch := sl_ne) only [sl_eq]
      unfold WB; unfold WT at h
      rcases h46 with h4 | h4 <;> rw [h4] <;> omega

/-! ## The recoded scalar -/

/-- `k + 16 Σ_{j<J} 32^j < 32^J` for `k < 2^b` and `J = ⌊(b + 6) / 5⌋`
(`Cfg.jwinJ`). -/
theorem recodeJ_lt {k b : Nat} (hk : k < 2 ^ b) :
    k + JacWinCfg.offset ((b + 6) / 5) < 32 ^ ((b + 6) / 5) := by
  rw [Weierstrass.X86_64.offset_eq]
  have hg := Window5.geom_mul ((b + 6) / 5)
  have h4 : 2 ^ b * 4 ≤ 32 ^ ((b + 6) / 5) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul, show 2 ^ b * 4 = 2 ^ (b + 2) by rw [Nat.pow_add]]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-! ## `[d]P` and `Z^(p-2)` -/

/-- What `mulQJ` writes, but the window method's recoded scalar and bits and
the power's: `K` and the window method's slots. -/
def mulJI : List Nat := otherJ ++ gridJ ++ [TMP] ++ [K]

theorem mulJI_idx : ∀ i ∈ mulJI, i = TMP ∨ 12 ≤ i := by decide

/-- What `mulQJ` and the power may write. -/
abbrev mulQJW (c : Cfg) : List (Nat × Nat) := winX c ++ slW c mulJI ++ pwW c

theorem mulQJ_w (hc : CfgOk c) : MulW c (mulQJW c) where
  fixed := (fixedOk_winX.append (fixedOk_slW mulJI_idx)).append fixedOk_pwW
  d := apart_append (apart_append (apart_winX (by decide)) (apart_slW (by decide))) (apart_pwW (by decide) (by decide))
  flag := fun w hw => by
    have := hc.n0
    rcases apart_append (apart_append (apart_winX (c := c) (i := FLAG) (by decide))
      (apart_slW (l := mulJI) (by decide))) (apart_pwW (by decide) (by decide)) w hw with h | h
    · exact Or.inl (by omega)
    · exact Or.inr h

/-- The Jacobian window method computes `[d]P` for `d < n` (`MulOk`), for four
or six words and a curve of prime order `n` with `n mod 32 ≥ 17`, with any
doubling `dbl` that doubles a Jacobian triple in place. -/
theorem mulQJ_ok (hc : CfgOk c) (h46 : c.n = 4 ∨ c.n = 6) (hC : Law c.C) (hO : PrimeOrder c.C)
    {dbl : Pt → Prog isa} (hD : DblOk c.MP' c.rcbSlots c.C dbl) (hn17 : 17 ≤ c.C.n % 32)
    (hn64 : 64 ≤ c.C.n) : MulOk c (Impl.Ecdh.X86_64.Cfg.mulQJ c dbl) (mulQJW c) := by
  intro base s hs g F hbp P hP hpx hpy hrep _ _ _ k hk hk8 _ ht₁ rest R h
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hJle := jwinJ_le hc
  unfold Impl.Ecdh.X86_64.Cfg.mulQJ
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
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WK <;> omega
  have hKW := sl_lt c (show K < WK by decide)
  have h32 : (32 : Nat) ^ Impl.Ecdh.X86_64.Cfg.jwinJ c ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (32 : Nat) = 2 ^ 5 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega
  have hBs : c.sl WB + 80 * c.n ≤ size := by
    simp (disch := sl_ne) only [sl_eq]; rcases h46 with h4 | h4 <;> rw [h4] <;> unfold WB <;> omega
  rw [Impl.Ecdh.X86_64.Cfg.jwinPrep]
  refine WP.seq (WP.seq ?_)
  rw [hK]
  refine WP.mono (addConst_ok hs₁ (n := c.n) (src := c.sl K) (dst := c.sl WK)
    (c := JacWinCfg.offset (Impl.Ecdh.X86_64.Cfg.jwinJ c)) h0 (sl_le c h7 (by decide)) (by omega)
    (Or.inl (by omega)) (by omega) (by omega))
    fun s₂ ⟨e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₂ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega) (by omega)
    (by omega) (by omega) (Or.inl (by omega))) fun s₃ ⟨b₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  rw [e₂] at b₃
  have U₃ : Unch base (winX c) s₁.mem s₃.mem :=
    ((O₂.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega)).unch.trans
      ((O₃.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega)).unch)).mono
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
      · exact lt_of_eq_of_lt F₃.onep (Nat.mod_lt _ (by omega))
    · show Rep _ (tmv c.C c.n base s₃ (c.sl PX)) (tmv c.C c.n base s₃ (c.sl PY))
        (tmv c.C c.n base s₃ (c.sl ONEP)) P
      rw [tv (by decide) (by decide), tv (by decide) (by decide), tv (by decide) (by decide)]; exact hrep
    · show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s₃.mem base (c.sl ONEP) c.n) = 1
      rw [F₃.onep, show 2 ^ (64 * c.n) % c.C.p = c.mont 1 by simp [Cfg.mont, Cfg.R], toM_cmont hc]; rfl
    · rw [hJ] at ht
      exact b₃ t (by omega)
  refine WP.mono (winJac_ok (jwLayQ hc h46) hpR hC hc.am3 hO hD hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hn17 hn64 hP
    (by rw [hJ]; exact hrec) hs₃ hM₃ hF) fun s₄ ⟨K₄, U₄, M₄, L₄, R₄⟩ => ?_
  rw [jwW_eq] at U₄
  have hs₄ := hs₃.of_keepRegs K₄ (rdi_not_powClob _)
  have F₄ := F₃.unch h7 hn (fixedOk_slW (by decide)) U₄
  have rz₄ : wordsVal s₄.mem base (c.sl RZ) c.n < c.C.p :=
    L₄ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  refine WP.seq (WP.mono (pPow_ok hc hs₄ M₄ rz₄ F₄.onep (fun h9 t ht => by
      rw [tbl_unch U₄ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht),
        tbl_unch U₃ h7 hn (j := 1) (by decide) ht (tbl_apart_winX (by decide) ht),
        tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
      exact ht₁ h9 t ht)) fun s₅ ⟨K₅, U₅, lt₅, v₅⟩ => h s₅ ?_)
  have r₅ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₅ i = sv c base s₄ i := fun hi h₁ =>
    sv_unch U₅ h7 hn hi (apart_pwW hi h₁)
  have c₂ : ∀ r ∈ [Reg.rax, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  have c₃ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  have c₁ : ∀ r ∈ [Reg.r8], r ∈ powClob c.n := fun r hr => by
    rw [List.mem_singleton.mp hr]; exact List.mem_cons_of_mem _ (r8_mem_clob _)
  have KK : KeepRegs (powClob c.n) s s₄ :=
    (((k₁.mono c₁).trans (k₂.mono c₂)).trans (k₃.mono c₃)).trans K₄
  refine ⟨hs₄.of_keepRegs K₅ (rdi_not_invClob _), by
      rw [K₅.gpr _ (rsi_not_invClob _), KK.gpr _ (rsi_not_powClob _)], by rw [K₅.rd, KK.rd],
    by rw [K₅.wr, KK.wr], ((U₁.trans U₃).trans (U₄.trans U₅)).mono ?_, fun _ hlt => ?_, lt₅, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_append.mp hw with hw | hw
      · exact List.mem_append_left _ (List.mem_append_right _ (slW_mono (by decide) hw))
      · exact List.mem_append_left _ (List.mem_append_left _ hw)
    · rcases List.mem_append.mp hw with hw | hw
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
