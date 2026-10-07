import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Weierstrass.X86_64.AddConst
import VerifiedGarbage.Proof.Weierstrass.X86_64.Bits
import VerifiedGarbage.Proof.Weierstrass.X86_64.Rep

/-!
# ECDH on x86-64: `[d]P` by windows, and `Z^(p-2)`

For up to nine words, the window method (as on AArch64,
`Proof/Ecdh/AArch64/Window.lean`): its slots are numbered slots, the table
of points slots `WT … WT + 23` past the tables of bits
(`winSlots_eq`), so they are apart as `window_ok` needs (`winLayQ`).
`winMul_ok` recodes `d` into `d + 8 Σ_{j<J} 16^j` and its bits (`winPrep`)
and runs the window method on the peer's point (or `G`), with `b R` in the
slot `BP` for the complete addition for `a = -3`. `mulPow_ok` is `mulQ`, the
window method or (for more words) the ladder, and the signature's power: it
leaves `R` representing `[d]P`.
-/

namespace VG.Proof.Ecdh.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass
open VG.Proof.Ecdsa.X86_64
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)
open VG.Impl.Ecdh.X86_64 (PX PY BP)

variable {c : Cfg}

/-! ## The slots -/

/-- The window method's configuration for ECDH. -/
abbrev winQ (c : Cfg) : WinCfg := c.winCfg PX PY BP

/-- The indices of the table's slots. -/
def tblI : List Nat := (List.range 24).map (WT + ·)

def roI : List Nat := [AP, BP, ZERO, PX, PY, ONEP]
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
theorem winIdx_lt : ∀ i ∈ roI ++ otherI ++ tblI, i < 107 ∧ i ≠ MP ∧ i ≠ TMP := by decide

/-- Every slot below `107` is in the working space, for up to nine words. -/
theorem sl_le_win (c : Cfg) (h9 : c.n ≤ 9) {i : Nat} (hi : i < 107) : c.sl i + 8 * c.n ≤ size := by
  rw [sl_eq]
  have := Nat.mul_le_mul_left (8 * c.n) hi
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 107 ≤ 8 * 9 * 107 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

theorem lay_win (h9 : c.n ≤ 9) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 107 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le_win c h9 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

theorem winW_eq (c : Cfg) : winW (winQ c) = slW c (otherI ++ tblI ++ [TMP]) := by
  rw [winW, winWs_eq]; simp only [slW, List.map_append, List.map_map]; rfl

theorem winLayQ (hc : CfgOk c) (h9 : c.n ≤ 9) : WinLay (winQ c) size := by
  have hn := hc.n0
  have hJ : (winQ c).J = c.winJ := rfl
  have hJle : c.winJ ≤ 16 * c.n + 1 := by unfold Cfg.winJ; have := hc.len_hi; omega
  have hJ1 : 1 ≤ c.winJ := by unfold Cfg.winJ; omega
  have hb : (winQ c).bits = c.sl WB := rfl
  have hK : (winQ c).tbl = c.sl WT := rfl
  have hMn : (winQ c).M.n = c.n := rfl
  refine ⟨?_, ?_, ?_, ?_, hn, ⟨by omega, by omega⟩, ?_, ?_⟩
  · rw [winSlots_eq]; exact lay_win h9 rfl rfl rfl winIdx_lt
  · exact map_sl_disj hn (l₁ := roI) (l₂ := otherI) (by decide)
  · exact map_sl_nodup hn (l := otherI) (by decide)
  · intro x hx
    have hx' : x ∈ (roI ++ otherI).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    have key : ∀ i ∈ roI ++ otherI, i < WT := by decide
    have := key i hi
    rw [hK, hMn]; exact Or.inl (sl_lt c this)
  · rw [hb, hJ, sl_eq]; show 64 + 8 * c.n * 73 + _ ≤ 8192
    have : 8 * c.n * 73 ≤ 8 * 9 * 73 := Nat.mul_le_mul_right _ (by omega)
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
      show 64 + 8 * c.n * 73 + 4 * c.winJ ≤ 64 + 8 * c.n * i
      have : 8 * c.n * 83 ≤ 8 * c.n * i := this
      have : 8 * c.n * 83 = 8 * c.n * 73 + 80 * c.n := by omega
      omega

theorem winXQ (hc : CfgOk c) (h9 : c.n ≤ 9) : WinX (winQ c) size where
  n := by show 1 ≤ c.n ∧ c.n ≤ 9; exact ⟨hc.n0, h9⟩
  tbl := by
    show c.sl WT < 2 ^ 31
    rw [sl_eq]; unfold WT; have : 8 * c.n * 83 ≤ 8 * 9 * 83 := Nat.mul_le_mul_right _ (by omega); omega
  exy := by show c.sl TY = c.sl TX + 8 * c.n; rw [sl_eq, sl_eq]; unfold TX TY; omega
  exz := by show c.sl TZ = c.sl TX + 16 * c.n; rw [sl_eq, sl_eq]; unfold TX TZ; omega

/-! ## The recoded scalar's areas -/

/-- The areas of the recoded scalar and of its bits. -/
def winX (c : Cfg) : List (Nat × Nat) := [(c.winK, 16 * c.n), (c.winBits, 80 * c.n)]

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

/-- Slot `i ≥ 71` is past the tables of bits `j < 3`. -/
theorem bits_le_sl {j t i : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hi : 71 ≤ i) :
    bitsAt c.n j + t + 1 ≤ c.sl i := by
  rw [bitsAt_eq, sl_eq]
  have := Nat.mul_le_mul_left (64 * c.n + 8) (show j ≤ 2 by omega)
  have := Nat.mul_le_mul_left (8 * c.n) hi
  have : 8 * c.n * 71 = 8 * c.n * 45 + 208 * c.n := by omega
  omega

theorem tbl_apart_winX {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) :
    ∀ w ∈ winX c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  simp only [winX, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact Or.inl (bits_le_sl hj ht (by decide))
  · exact Or.inl (bits_le_sl hj ht (by decide))

/-- A table of bits is apart from numbered slots below the tables or past the
inversion's working area. -/
theorem tbl_apart_slW' {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∨ 71 ≤ i) {j t : Nat} (hj : j < 3)
    (ht : t < 64 * c.n) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · exact Or.inr (sl_below_bits c h j t)
  · exact Or.inl (bits_le_sl hj ht h)

theorem offset_eq (J : Nat) : WinCfg.offset J = 8 * geom J := by
  have := geom_mul J
  unfold WinCfg.offset
  omega

/-! ## `[d]P` by windows -/

/-- What the window method leaves: `R` represents `[k]P`. -/
structure WinMulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  keep : KeepRegs (powClob c.n) s s'
  unch : Unch base (winX c ++ slW c (otherI ++ tblI ++ [TMP])) s.mem s'.mem
  mod : ModOkW c.MP' size c.C.p s'.mem base
  lt : ∀ x ∈ [c.sl RX, c.sl RY, c.sl RZ], wordsVal s'.mem base x c.n < c.C.p
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)

/-- `k + 8 Σ_{j<J} 16^j` and its bits, from the slot `ks`, then the window
method on `P`: `[k]P`. -/
theorem winMul_ok (hc : CfgOk c) (h9 : c.n ≤ 9) (hC : Law c.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {ks : Nat} (hks : ks < 45)
    (hk8 : sv c base s ks < 2 ^ (8 * c.C.len)) {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinMulPost c base P (sv c base s ks) s s' → WP isa rest s' R) :
    WP isa (.seq (.seq (c.winPrep (c.sl ks)) (WinCfg.window (winQ c))) rest) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  have hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega)
  have hrec : wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ < 16 ^ c.winJ := recode_lt_len hk8
  have hJle : c.winJ ≤ 16 * c.n + 1 := by unfold Cfg.winJ; have := hc.len_hi; omega
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
  refine WP.mono (window_ok (winLayQ hc h9) (winXQ hc h9) hpR hC hc.am3 hP hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hs₂ hM₂ hF
    (by rw [hJ]; exact hrec) (Nat.le_add_left _ _)) fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => h s₃ ?_
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

/-! ## `[d]P`, by windows or the ladder, and `Z^(p-2)` -/

/-- What `mulQ` (the window method or the ladder) and the power may write. -/
def mulI : List Nat := otherI ++ tblI ++ [TMP] ++
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP]

theorem mulI_idx : ∀ i ∈ mulI, i = TMP ∨ 12 ≤ i := by decide

/-- A numbered slot below the tables not in `mulI`, apart from what it writes. -/
theorem apart_mulW {i : Nat} (hi : i < 45) (h₁ : i ∉ mulI) (h₂ : i ∉ [ACC, PT, TMP]) :
    ∀ w ∈ winX c ++ slW c mulI ++ pwW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_append (apart_winX hi) (apart_slW h₁)) (apart_pwW hi h₂)

theorem fixedOk_mulW : FixedOk c (winX c ++ slW c mulI ++ pwW c) :=
  (fixedOk_winX.append (fixedOk_slW mulI_idx)).append fixedOk_pwW

/-- What `mulQ` and the power leave: `R` represents `[k]P`. -/
structure MulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ invClob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (winX c ++ slW c mulI ++ pwW c) s.mem s'.mem
  q : Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- `[k]P`, for `k` at `K` (and its bits in the first table), by windows for
up to nine words and by the ladder for more, then `Z^(p-2)`. -/
theorem mulPow_ok (hc : CfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    {k : Nat} (hk : sv c base s K = k) (hk8 : k < 2 ^ (8 * c.C.len))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', MulPost c base P k s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdh.X86_64.Cfg.mulQ c) (.seq c.pPow rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Impl.Ecdh.X86_64.Cfg.mulQ
  split
  · rename_i h9
    refine winMul_ok hc h9 hC hs F hbp hP hpx hpy hrep (ks := K) (by decide) (hk ▸ hk8) fun s₃ W => ?_
    have F₃ := F.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
    have rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := W.lt _ (by simp)
    refine WP.seq (WP.mono (pPow_ok hc W.scr W.mod rz₃ F₃.onep (fun t ht => by
        rw [tbl_unch W.unch h7 hn (j := 1) (by decide) ht (apart_append (tbl_apart_winX (by decide) ht)
          (tbl_apart_slW' (by decide) (by decide) ht))]
        exact ht₁ t ht)) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
    have r₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
      sv_unch U₄ h7 hn hi (apart_pwW hi h₁)
    refine ⟨W.scr.of_keepRegs K₄ (rdi_not_invClob _), fun r hr => ?_, by rw [K₄.rd, W.keep.rd],
      by rw [K₄.wr, W.keep.wr], (W.unch.trans U₄).mono ?_, ?_, lt₄, ?_, ?_⟩
    · rw [K₄.gpr r hr, W.keep.gpr r (fun h => hr (List.mem_cons_of_mem _ h))]
    · intro w hw
      simp only [mulI, slW, List.map_append, List.mem_append] at hw ⊢
      rcases hw with (hw | hw) | hw
      · exact Or.inl (Or.inl hw)
      · exact Or.inl (Or.inr (Or.inl hw))
      · exact Or.inr hw
    · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
      rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
        r₄ (i := RZ) (by decide) (by decide), ← hk]
      exact W.q
    · show _ = toM _ _ (sv c base s₄ RZ) ^ _
      rw [r₄ (i := RZ) (by decide) (by decide)]
      exact v₄
    · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃
  · have hk' : k < 2 ^ (64 * c.n) := hk ▸ wordsVal_lt _ _ _ _
    have hstep := step_rep (L := Impl.Ecdh.X86_64.Cfg.ladderQ c) (k := k) hC hP
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
        rw [F.ap]; exact toM_cmont hc _)
      (by
        show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
        rw [F.b3p]; exact toM_cmont hc _)
      hrep
    refine ladPow_ok hc hs F hstep (by rw [shiftRight_eq_zero hk', mul_zero_pt]; exact rep_infinity' hC)
      hpx hpy hrx hry hrz ht₀ ht₁ fun s₅ L => h s₅ ?_
    refine ⟨L.scr, L.gpr, L.rd, L.wr, L.unch.mono ?_, by have := L.q; rwa [Nat.shiftRight_zero] at this,
      L.acc_lt, L.acc, L.rz_lt⟩
    intro w hw
    simp only [mulI, slW, List.map_append, List.mem_append] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (Or.inr (Or.inr hw))
    · exact Or.inr hw

end VG.Proof.Ecdh.X86_64
