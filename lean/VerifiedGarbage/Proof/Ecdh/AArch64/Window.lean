import VerifiedGarbage.Proof.Ecdh.AArch64.Validate
import VerifiedGarbage.Proof.Ecdsa.AArch64.CombLays
import VerifiedGarbage.Proof.Weierstrass.AArch64.AddConst

/-!
# ECDH on AArch64: `[d]P` by windows, and `Z^(p-2)`

The window method's slots are numbered slots, the table of points slots
`WT … WT + 23` past the signature's tables of bits, and the recoded scalar
and its bits where its unused tables `j = 1, 2` are (`winSlots_eq`), so they
are apart as `window_ok` needs (`winLayQ`). `winPow_ok` recodes `d` into
`d + 8 Σ_{j<J} 16^j` and its bits (`winPrep`), runs the window method on the
peer's point (or `G`) and the signature's power, and leaves `R` representing
`[d]P`.
-/

namespace VG.Proof.Ecdh.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.AArch64
open VG.Proof.Ed25519.AArch64 (Keeps Keeps.trans Keeps.mono)
open VG.Impl.Ecdh.AArch64 (PX PY)

variable {c : Cfg}

/-! ## The slots -/

/-- The window method's configuration for ECDH. -/
abbrev winQ (c : Cfg) : WinCfg := c.winCfg PX PY

/-- The indices of the table's slots. -/
def tblI : List Nat := (List.range 24).map (WT + ·)

def roI : List Nat := [AP, BM, ZERO, PX, PY, ONEP]
def otherI : List Nat := [RX, RY, RZ, TX, TY, TZ, PT, T0, T1, T2, T3, T4, T5, DX, DY, DZ]

theorem winTblSlots_eq (c : Cfg) : winTblSlots (winQ c) = tblI.map c.sl := by
  simp only [winTblSlots, tblI, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show c.sl WT + 8 * c.n * i = c.sl (WT + i)
  rw [sl_eq, sl_eq, Nat.mul_add, Nat.add_assoc]

theorem winSlots_eq (c : Cfg) : winSlots (winQ c) = (roI ++ otherI ++ tblI).map c.sl := by
  rw [winSlots, winTblSlots_eq, List.map_append, List.map_append]; rfl

theorem winWs_eq (c : Cfg) : winWs (winQ c) = (otherI ++ tblI).map c.sl := by
  rw [winWs, winTblSlots_eq, List.map_append]; rfl

/-- The indices of the window method's slots. -/
theorem winIdx_lt : ∀ i ∈ roI ++ otherI ++ tblI, i < 112 ∧ i ≠ MP ∧ i ≠ TMP := by decide

/-- Every slot below `112` is in the working space. -/
theorem sl_le' (c : Cfg) (hn : c.n < 10) {i : Nat} (hi : i < 112) : c.sl i + 8 * c.n ≤ size := by
  rw [sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 112 ≤ 8 * 9 * 112 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

theorem lay_map' (hc : CfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 112 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le' c hc.n10 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem winW_eq (c : Cfg) : winW (winQ c) = slW c (otherI ++ tblI ++ [TMP]) := by
  rw [winW, winWs_eq]; simp only [slW, List.map_append, List.map_map]; rfl

theorem winLayQ (hc : CfgOk c) : WinLay (winQ c) size := by
  have hn := hc.n0
  have h7 := hc.n10
  have hJ : (winQ c).J = 16 * c.n + 1 := rfl
  have hb : (winQ c).bits = c.sl WB := rfl
  have hK : (winQ c).tbl = c.sl WT := rfl
  have hMn : (winQ c).M.n = c.n := rfl
  refine ⟨?_, ?_, ?_, ?_, hn, ⟨by omega, by omega⟩, ?_, ?_, ?_⟩
  · rw [winSlots_eq]; exact lay_map' hc rfl rfl rfl winIdx_lt
  · exact map_sl_disj hn (l₁ := roI) (l₂ := otherI) (by decide)
  · exact map_sl_nodup hn (l := otherI) (by decide)
  · intro x hx
    have hx' : x ∈ (roI ++ otherI).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    have key : ∀ i ∈ roI ++ otherI, i < WT := by decide
    have := key i hi
    rw [hK, hMn]; exact Or.inl (sl_lt c this)
  · rw [hb, hJ, sl_eq]; show 64 + 8 * c.n * 55 + _ ≤ 8192
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega)
    omega
  · rw [hb, sl_eq]; show 64 + 8 * c.n * 55 + 3 < 4096
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega)
    omega
  · intro w hw
    rw [winW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hb, hJ]
    have key : ∀ i ∈ otherI ++ tblI ++ [TMP], i < WB ∨ WT ≤ i := by decide
    rcases key i hi with h | h
    · exact Or.inr (sl_lt c h)
    · refine Or.inl ?_
      have := Nat.mul_le_mul_left (8 * c.n) h
      dsimp only
      rw [sl_eq, sl_eq]
      show 64 + 8 * c.n * 55 + 4 * (16 * c.n + 1) ≤ 64 + 8 * c.n * i
      have : 8 * c.n * 87 ≤ 8 * c.n * i := this
      have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega
      omega

theorem winAQ (c : Cfg) : WinA (winQ c) where
  sl x hx := by
    rw [winSlots_eq] at hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact sl_mod8 c i
  mod := MP'_A c

/-! ## The recoded scalar's areas -/

/-- The areas of the recoded scalar and of its bits. -/
def winX (c : Cfg) : List (Nat × Nat) := [(c.winK, 16 * c.n), (c.winBits, 64 * (c.n + 1))]

theorem fixedOk_winX : FixedOk c (winX c) := by
  intro w hw
  simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < WK by decide)))
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (show 12 < WB by decide)))

/-- A slot below the tables of bits is apart from them. -/
theorem apart_winX {i : Nat} (hi : i < 45) :
    ∀ w ∈ winX c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (sl_lt c (show i < WK by unfold WK; omega))
  · exact Or.inl (sl_lt c (show i < WB by unfold WB; omega))

/-- Slot `i ≥ 69` is past the tables of bits `j < 3`. -/
theorem bits_le_sl {j t i : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hi : 69 ≤ i) :
    bitsAt c.n j + t + 1 ≤ c.sl i := by
  rw [bitsAt_eq, sl_eq]
  have := Nat.mul_le_mul_left (64 * c.n) (show j ≤ 2 by omega)
  have := Nat.mul_le_mul_left (8 * c.n) hi
  omega

theorem tbl_apart_slW' {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∨ 69 ≤ i) {j t : Nat} (hj : j < 3)
    (ht : t < 64 * c.n) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · exact Or.inr (sl_below_bits c h j t)
  · exact Or.inl (bits_le_sl hj ht h)

/-- The flag word survives the window method and the power. -/
theorem flag_unch_win {base : Addr} {l₁ : List Nat} {m m' : Mem}
    (hu : Unch base (winX c ++ (slW c l₁ ++ chainWc c)) m m') (h7 : c.n < 10) (h0 : 0 < c.n)
    (hn : base.toNat + size ≤ 2 ^ 64) (hl₁ : FLAG ∉ l₁) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_append (apart_winX (c := c) (i := FLAG) (by decide))
    (apart_append (apart_slW hl₁) (apart_chainWc (c := c) (i := FLAG) (by decide) (by decide))) w hw
    with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem offset_eq (J : Nat) : WinCfg.offset J = 8 * geom J := by
  have := geom_mul J
  unfold WinCfg.offset
  omega

/-! ## `[d]P` and `Z^(p-2)` -/

/-- What the window method leaves: `R` represents `[k]P`. -/
structure WinMulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ combClob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (winX c ++ slW c (otherI ++ tblI ++ [TMP])) s.mem s'.mem
  mod : ModOkA c.MP' size c.C.p s'.mem base
  lt : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

theorem combClob_sub {n : Nat} : ∀ r ∈ [Reg.x1, .x2, .x5, .x16, .x17, .x19], r ∈ combClob n := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact combClob_mem (by simp)
  · exact combClob_mem (by simp)
  · exact combClob_mem (by simp)
  · exact combClob_mem (by simp)
  · exact combClob_mem (by simp)
  · simp [combClob]

/-- `k + 8 Σ_{j<J} 16^j` and its bits, from the slot `ks`, then the window
method on `P`: `[k]P`. -/
theorem winMul_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {ks : Nat} (hks : ks < 45)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinMulPost c base P (sv c base s ks) s s' → WP isa rest s' R) :
    WP isa (.seq (c.winPrep (c.sl ks)) (.seq (WinCfg.window (winQ c)) rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hk : wordsVal s.mem base (c.sl ks) c.n < 2 ^ (64 * c.n) := wordsVal_lt _ _ _ _
  have hrec := recode_lt hk
  have hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le' c h7 (i := WK + 1) (by decide)
    rw [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega
  have hKW := sl_lt c (show ks < WK by unfold WK; omega)
  have h16 : (16 : Nat) ^ (16 * c.n + 1) ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hJ : (winQ c).J = 16 * c.n + 1 := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  have e69 : c.sl WK + 16 * c.n = c.sl WB := by rw [sl_eq, sl_eq]; unfold WK WB; omega
  have hB4 : c.sl WB + 8 ≤ 4096 := by
    rw [sl_eq]; unfold WB
    have : 8 * c.n * 55 ≤ 8 * 9 * 55 := Nat.mul_le_mul_right _ (by omega)
    omega
  have hBs : c.sl WB + 64 * (c.n + 1) ≤ c.sl WT := by
    rw [sl_eq, sl_eq]; unfold WB WT
    have : 8 * c.n * 87 = 8 * c.n * 55 + 256 * c.n := by omega
    omega
  have hTs := sl_le' c h7 (i := WT) (by decide)
  rw [Cfg.winPrep]
  refine WP.seq (WP.seq ?_)
  rw [hK, offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl ks) (dst := c.sl WK)
    (c := 8 * geom (16 * c.n + 1)) h0 h7 (sl_le c h7 hks) (by omega) (sl_mod8 c _) (sl_mod8 c _)
    (Or.inl (by omega)) (by omega) (by omega)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (x0_not_clob _)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega) (by omega)
    (by omega) (by omega) (by omega) hB4 (Or.inl (by omega))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  have U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 64 * (c.n + 1)) (Nat.le_refl _) (by omega)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  have F₂ := F.unch h7 hn fixedOk_winX U₂
  have e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX hi)
  have hM₂ := modP_of hc F₂.mp
  have tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  have hF : WinFixed (winQ c) c.C base s₂ P (wordsVal s.mem base (c.sl ks) c.n + 8 * geom (16 * c.n + 1)) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₂.zero, ?_, fun t ht => ?_⟩
    · show toM _ _ (wordsVal s₂.mem _ (c.sl AP) c.n) = _; rw [F₂.ap]; exact toM_cmont hc _
    · show toM _ _ (wordsVal s₂.mem _ (c.sl BM) c.n) = _; rw [F₂.bm]; exact toM_cmont hc _
    · simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₂.ap (hmont _)
      · exact lt_of_eq_of_lt F₂.bm (hmont _)
      · exact lt_of_eq_of_lt F₂.zero (by omega)
      · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide)) hpy
      · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega))
    · show Rep _ (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide), tv (by decide), tv (by decide)]; exact hrep
    · rw [hJ] at ht
      exact b₂ t (by omega)
  refine WP.seq (WP.mono (window_ok (winLayQ hc) (winAQ c) hpR hC hc.am3 hP hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hs₂ hM₂ hF
    (by rw [hJ]; exact hrec) (Nat.le_add_left _ _)) fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => h s₃ ?_)
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  have nc : ∀ {r}, r ∉ combClob c.n → r ∉ clob c.n := fun hr h => hr (clob_combClob _ h)
  exact ⟨hs₂.of_keepRegs K₃ (x0_not_combClob h7), fun r hr => by
      rw [K₃.gpr r hr, k₂.gpr r (fun h => hr (combClob_sub r h)), k₁.gpr r (nc hr)],
    by rw [K₃.rd, k₂.rd, k₁.rd], by rw [K₃.wr, k₂.wr, k₁.wr], U₂.trans U₃, M₃, L₃, R₃⟩

/-- What the window method and the power leave: `R` represents `[k]P`. -/
structure WinPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ combClob c.n → r ∉ powClob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (winX c ++ (slW c (otherI ++ tblI ++ [TMP]) ++ chainWc c)) s.mem s'.mem
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- `[d]P` by windows, then `Z^(p-2)`. -/
theorem winPow_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) {P : Point c.C} (hP : onCurve c.C P = true)
    (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinPost c base P (sv c base s K) s s' → WP isa rest s' R) :
    WP isa (.seq (c.winPrep (c.sl K)) (.seq (WinCfg.window (winQ c)) (.seq c.pPow rest))) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  refine winMul_ok hc hC hs F hP hpx hpy hrep (ks := K) (by decide) fun s₃ W => ?_
  have F₃ := F.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
  have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := W.lt _ (by simp)
  refine WP.seq (WP.mono (pPow_ok hc W.scr W.mod rz₃)
    fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
  have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
    sv_unch U₄ h7 hn hi (apart_chainWc hi h₁)
  refine ⟨W.scr.of_keepRegs K₄ (x0_not_powClob h7), fun r hr hr' => ?_, by rw [K₄.rd, W.rd],
    by rw [K₄.wr, W.wr], (W.unch.trans U₄).mono (by simp), ?_, lt₄, ?_, ?_⟩
  · rw [K₄.gpr r hr', W.gpr r hr]
  · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
    rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
      r₄ (i := RZ) (by decide) (by decide)]
    exact W.q
  · show _ = toM _ _ (sv c base s₄ RZ) ^ _
    rw [r₄ (i := RZ) (by decide) (by decide)]
    exact v₄
  · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.AArch64
