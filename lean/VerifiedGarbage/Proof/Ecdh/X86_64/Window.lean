module

public import VerifiedGarbage.Impl.Ecdh.X86_64
public import VerifiedGarbage.Proof.Ecdsa.X86_64.Inv
public import VerifiedGarbage.Proof.Weierstrass.X86_64.WinEntry
import VerifiedGarbage.Proof.Ecdh.X86_64.Validate
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulFn
import VerifiedGarbage.Proof.Weierstrass.X86_64.WinLoop
import VerifiedGarbage.Proof.Ecdsa.X86_64.MulBase
import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Weierstrass.JacMadd
public import VerifiedGarbage.Impl.Weierstrass.X86_64.Window
public import VerifiedGarbage.Proof.Mont.X86_64.Csub
import VerifiedGarbage.Proof.Weierstrass.X86_64.Copy
import VerifiedGarbage.Proof.Mont.X86_64.WideOps
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Weierstrass.MontContract

/-! ### `Weierstrass.X86_64.AddConst`, which this module and modules that import it used -/

section

/-!
# The window method on x86-64: the recoded scalar

`addConst n src dst c` writes `c` to `dst`, adds the `n` words at `src` to the
low `n` words of `dst` by the carry chain (`chainWAdd_ok`), and adds the carry
to its top word (`adcTop_ok`): `[dst] = [src] + c` when the sum fits
(`addConst_ok`).
-/

@[expose] public section

namespace VG.Proof.Weierstrass.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass
open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- `[d] += CF`, through `r8`. -/
theorem adcTop_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d : Nat} (hd : d + 8 ≤ size)
    {cf : Bool} (hc : s.cf = some cf) :
    WP isa (.block [.mov .r8 (.mem (sc d)), .alu .adc .r8 (.imm 0), .store (sc d) .r8]) s fun t =>
      t.mem = s.mem.writeW (off base d) (word s.mem base d + (BitVec.ofBool cf).setWidth 64) ∧
        KeepRegs [.r8] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  refine WP.mono (movMem_ok hs .r8 hd) fun u ⟨lu, cu, ku⟩ => ?_
  rw [← List.singleton_append, WP.block_append_iff]
  have ha : WP isa (.block [.alu .adc .r8 (.imm 0)]) u fun v =>
      v.gpr .r8 = word s.mem base d + (BitVec.ofBool cf).setWidth 64 ∧ Keeps [.r8] u v := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
      Option.map_some, cu, hc, lu, RegUpd.gpr_setReg, ite_true, Option.some.injEq, exists_eq_left']
    refine ⟨by simp, fun r hr => ?_,
      rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]
  refine WP.mono ha fun v ⟨av, kv⟩ => ?_
  have hsv := (hs.of_keeps ku (by decide)).of_keeps kv (by decide)
  refine WP.mono (storeReg_ok hsv .r8 hd) fun t ⟨mt, _, _, kt⟩ => ⟨?_, ?_⟩
  · rw [mt, av, kv.2.1, ku.2.1]
  · exact ((Keeps.regs ku).trans (Keeps.regs kv)).trans (kt.mono (by decide))

/-- `[dst] = [src] + c`, `n + 1` words from `n`. -/
theorem addConst_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {n src dst c : Nat}
    (h0 : 0 < n) (hsrc : src + 8 * n ≤ size) (hdst : dst + 8 * (n + 1) ≤ size)
    (hsep : src + 8 * n ≤ dst ∨ dst + 8 * (n + 1) ≤ src) (hc : c < 2 ^ (64 * (n + 1)))
    (hsum : wordsVal s.mem base src n + c < 2 ^ (64 * (n + 1))) :
    WP isa (.block (WinCfg.addConst n src dst c)) s fun t =>
      wordsVal t.mem base dst (n + 1) = wordsVal s.mem base src n + c ∧ KeepRegs [.rax, .r8] s t ∧
      Outside base dst (8 * (n + 1)) s.mem t.mem := by
  have hn := hs.nowrap
  rw [WinCfg.addConst, List.append_assoc, WP.block_append_iff]
  refine WP.mono (setConst_ok hs (n := n + 1) (o := dst) (x := c) hdst hc) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  have hs₁ := hs.of_keepRegs k₁ (by decide)
  have vs₁ : wordsVal s₁.mem base src n = wordsVal s.mem base src n := O₁.wordsVal (by omega_using [hsep]) (by omega_using [hsrc, hn])
  rw [WP.block_append_iff]
  refine WP.mono (chainWAdd_ok n (op := .add) (c := false) (t := dst) (a := dst) (b := src) hs₁
    (Or.inl ⟨rfl, rfl⟩) (Or.inl h0) (by omega_using [hdst]) (by omega_using [hdst]) (by omega_using [hsrc]) (Or.inl rfl)
    (by unfold Near; omega_using [hsep])) fun s₂ ⟨c', hc₂, e₂, k₂, O₂⟩ => ?_
  have hs₂ := hs₁.of_keepRegs k₂ (by decide)
  refine WP.mono (adcTop_ok hs₂ (d := dst + 8 * n) (by omega_using [hdst]) hc₂) fun t ⟨mt, kt⟩ => ?_
  -- The words of `c`, and the top word.
  have hc₁ := e₁
  rw [wordsVal_succ_top] at hc₁
  have htop₂ : word s₂.mem base (dst + 8 * n) = word s₁.mem base (dst + 8 * n) := O₂.word (by omega_using []) (by omega_using [hdst, hn])
  have hlow : wordsVal t.mem base dst n = wordsVal s₂.mem base dst n := by
    rw [mt]; exact (writeW_outside _ _ _ (by omega_using [hdst, hn])).wordsVal (by omega_using []) (by omega_using [hdst, hn])
  rw [vs₁] at e₂
  simp only [Bool.toNat_false, Nat.add_zero] at e₂
  have hb : (BitVec.ofBool c').setWidth 64 = BitVec.ofNat 64 c'.toNat := by cases c' <;> rfl
  -- The top word does not wrap.
  have hpow : 2 ^ (64 * (n + 1)) = 2 ^ (64 * n) * 2 ^ 64 := by rw [Nat.mul_succ, Nat.pow_add]
  generalize hT : (word s₁.mem base (dst + 8 * n)).toNat = T at hc₁
  generalize hXd : 2 ^ (64 * n) = X at hc₁ e₂ hpow
  have hfit : T + c'.toNat < 2 ^ 64 := by
    have h1 : X * (T + c'.toNat) ≤ wordsVal s.mem base src n + c := by
      rw [Nat.mul_add]; omega_using [hc₁, e₂]
    rw [hpow] at hsum
    exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt h1 hsum)
  have htop : (word t.mem base (dst + 8 * n)).toNat = T + c'.toNat := by
    rw [mt, word_writeW_self, htop₂, hb, BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show c'.toNat < 2 ^ 64 by cases c' <;> decide), hT, Nat.mod_eq_of_lt hfit]
  refine ⟨?_, ?_, ?_⟩
  · rw [wordsVal_succ_top, hlow, htop, hXd, Nat.mul_add]
    omega_using [hc₁, e₂]
  · exact ((k₁.mono (by decide)).trans (k₂.mono (by decide))).trans (kt.mono (by decide))
  · have O₃ : Outside base (dst + 8 * n) 8 s₂.mem t.mem := by rw [mt]; exact writeW_outside _ _ _ (by omega_using [hdst, hn])
    exact (O₁.trans ((O₂.mono (Nat.le_refl _) (by omega_using [])).trans (O₃.mono (by omega_using []) (by omega_using []))))

end VG.Proof.Weierstrass.X86_64

end

end

/-!
# ECDH on x86-64: `[d]P` by windows, and `Z^(p-2)`

For up to nine words, the window method (as on AArch64,
`Proof/Ecdh/AArch64/Window.lean`): its slots are numbered slots, the table
of points slots `WT … WT + 23` past the tables of bits
(`winSlots_eq`), so they are apart as `window_ok` needs (`winLayQ`).
`winMul_ok` recodes `d` into `d + 8 Σ_{j<J} 16^j` and its bits (`winPrep`)
and runs the window method on the peer's point (or `G`), with `b R` in the
slot `BP` for the complete addition for `a = -3`. `mulPow_ok` is `mulQ`, the
window method or (for more words) the ladder, inline or by a call of
`vg_<curve>_mul`, and the signature's power: it leaves `R` representing `[d]P`.
-/

@[expose] public section

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
  simp (disch := sl_ne) only [sl_eq]; rw [Nat.mul_add, Nat.add_assoc]

theorem winSlots_eq (c : Cfg) : winSlots (winQ c) = (roI ++ otherI ++ tblI).map c.sl := by
  rw [winSlots, winTblSlots_eq, List.map_append, List.map_append]; rfl

theorem winWs_eq (c : Cfg) : winWs (winQ c) = (otherI ++ tblI).map c.sl := by
  rw [winWs, winTblSlots_eq, List.map_append]; rfl

/-- The indices of the window method's slots. -/
theorem winIdx_lt : ∀ i ∈ roI ++ otherI ++ tblI, i < 108 ∧ i ≠ MP ∧ i ≠ TMP := by decide

/-- Every slot below `108` is in the working space, for up to nine words. -/
theorem sl_le_win (c : Cfg) (h9 : c.n ≤ 9) {i : Nat} (hi : i < 108) : c.sl i + 8 * c.n ≤ size := by
  obtain hix : ix c i < 108 := by
    have := tk_le c
    rcases ix_cases c i with ⟨_, _, h⟩ | ⟨_, _, h⟩ | h <;> rw [h] <;> first | decide | omega_arith
  rw [sl_eq']
  have := Nat.mul_le_mul_left (8 * c.n) hix
  rw [Nat.mul_succ] at this
  have : 8 * c.n * 108 ≤ 8 * 9 * 108 := Nat.mul_le_mul_right _ (by omega_arith)
  show _ ≤ 8192
  omega_arith

theorem lay_win (h9 : c.n ≤ 9) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 108 ∧ i ≠ MP ∧ i ≠ TMP) :
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

theorem winLayQ (hc : BaseCfgOk c) (h9 : c.n ≤ 9) : WinLay (winQ c) size := by
  have hn := hc.n0
  have hJ : (winQ c).J = c.winJ := rfl
  obtain hJle : c.winJ ≤ 16 * c.n + 1 := by
    unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega_arith
  obtain hJ1 : 1 ≤ c.winJ := by unfold Cfg.winJ; omega_arith
  have hb : (winQ c).bits = c.sl WB := rfl
  have hK : (winQ c).tbl = c.sl WT := rfl
  have hMn : (winQ c).M.n = c.n := rfl
  refine ⟨?_, ?_, ?_, ?_, hn, ⟨by omega_arith, by omega_arith⟩, ?_, ?_⟩
  · rw [winSlots_eq]; exact lay_win h9 rfl rfl rfl winIdx_lt
  · exact map_sl_disj hn (l₁ := roI) (l₂ := otherI) (by decide)
  · exact map_sl_nodup hn (l := otherI) (by decide)
  · intro x hx
    obtain hx' : x ∈ (roI ++ otherI).map c.sl := by rw [List.map_append]; exact hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx'
    obtain key : ∀ i ∈ roI ++ otherI, i < WT := by decide
    have := key i hi
    rw [hK, hMn]; exact Or.inl (sl_lt c this)
  · rw [hb, hJ]; simp (disch := sl_ne) only [sl_eq]; show 64 + 8 * c.n * 73 + _ ≤ 8192
    have : 8 * c.n * 73 ≤ 8 * 9 * 73 := Nat.mul_le_mul_right _ (by omega_arith)
    omega_arith
  · intro w hw
    rw [winW_eq] at hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    rw [hb, hJ]
    obtain key : ∀ i ∈ otherI ++ tblI ++ [TMP], i < WB ∨ WT ≤ i := by decide
    rcases key i hi with h | h
    · by_cases h6 : i = TMP ∧ c.n = 6
      · obtain ⟨rfl, h6⟩ := h6
        refine Or.inl ?_
        dsimp only
        rw [sl_eq' c TMP, ix_tmp6 c h6]
        simp (disch := sl_ne) only [sl_eq]
        show 64 + 8 * c.n * 73 + 4 * c.winJ ≤ 64 + 8 * c.n * 83
        have : 8 * c.n * 83 = 8 * c.n * 73 + 80 * c.n := by omega_arith
        omega_arith
      · exact Or.inr (sl_lt c h (by
          by_cases ht : i = TMP
          · exact .inr (.inr ⟨fun e => h6 ⟨ht, e⟩, by decide⟩)
          · exact .inl ht))
    · refine Or.inl ?_
      have := Nat.mul_le_mul_left (8 * c.n) h
      dsimp only
      simp (disch := sl_ne) only [sl_eq]
      show 64 + 8 * c.n * 73 + 4 * c.winJ ≤ 64 + 8 * c.n * i
      have : 8 * c.n * 84 ≤ 8 * c.n * i := this
      have : 8 * c.n * 84 = 8 * c.n * 73 + 88 * c.n := by omega_arith
      omega_arith

theorem winXQ (hc : BaseCfgOk c) (h9 : c.n ≤ 9) : WinX (winQ c) size where
  n := by show 1 ≤ c.n ∧ c.n ≤ 9; exact ⟨hc.n0, h9⟩
  tbl := by
    show c.sl WT < 2 ^ 31
    simp (disch := sl_ne) only [sl_eq]; unfold WT; have : 8 * c.n * 84 ≤ 8 * 9 * 84 := Nat.mul_le_mul_right _ (by omega_arith); omega_arith
  exy := by show c.sl TY = c.sl TX + 8 * c.n; simp (disch := sl_ne) only [sl_eq]; unfold TX TY; omega_arith
  exz := by show c.sl TZ = c.sl TX + 16 * c.n; simp (disch := sl_ne) only [sl_eq]; unfold TX TZ; omega_arith

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
  by_cases h6 : i = TMP ∧ c.n = 6
  · obtain ⟨rfl, h6⟩ := h6
    rw [sl_eq' c TMP, ix_tmp6 c h6]
    rcases hw with rfl | rfl
    · refine Or.inr ?_
      show c.winK + 16 * c.n ≤ _
      unfold Cfg.winK; simp (disch := sl_ne) only [sl_eq]; unfold WK; omega_arith
    · refine Or.inr ?_
      show c.winBits + 80 * c.n ≤ _
      unfold Cfg.winBits; simp (disch := sl_ne) only [sl_eq]; unfold WB; omega_arith
  · have hT : i ≠ TMP ∨ 83 < WK ∨ (c.n ≠ 6 ∧ 55 < WK) := by
      by_cases ht : i = TMP
      · exact .inr (.inr ⟨fun e => h6 ⟨ht, e⟩, by decide⟩)
      · exact .inl ht
    obtain hT' : i ≠ TMP ∨ 83 < WB ∨ (c.n ≠ 6 ∧ 55 < WB) := by
      by_cases ht : i = TMP
      · exact .inr (.inr ⟨fun e => h6 ⟨ht, e⟩, by decide⟩)
      · exact .inl ht
    rcases hw with rfl | rfl
    · exact Or.inl (sl_lt c (show i < WK by unfold WK; omega_arith) hT)
    · exact Or.inl (sl_lt c (show i < WB by unfold WB; omega_arith) hT')

/-- Slot `i ≥ 71` is past the tables of bits `j < 3` (but slot `83` for six
words, in the temporary area's place). -/
theorem bits_le_sl {j t i : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hi : 71 ≤ i)
    (h83 : i ≠ 83 ∨ c.n ≠ 6 := by first | exact .inl (by decide) | exact .inr (by omega_arith)) :
    bitsAt c.n j + t + 1 ≤ c.sl i := by
  obtain hix : ix c i = i := by
    have hT : TMP = 2 := rfl
    unfold ix
    repeat' split
    all_goals omega_arith
  rw [bitsAt_eq, sl_eq', hix]
  have := Nat.mul_le_mul_left (64 * c.n + 8) (show j ≤ 2 by omega_arith)
  have := Nat.mul_le_mul_left (8 * c.n) hi
  have : 8 * c.n * 71 = 8 * c.n * 45 + 208 * c.n := by omega_arith
  omega_arith

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
    (ht : t < 64 * c.n) (hT : TMP ∉ l ∨ j ≠ 1 ∨ c.n ≠ 9 := by
      first | exact .inl (by decide) | exact .inr (.inl (by decide)) | exact .inr (.inr (by omega_arith))) :
    ∀ w ∈ slW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  rcases hl i hi with h | h
  · rcases sl_apart_bits c h (hT.elim (fun h' => .inl fun e => h' (e ▸ hi)) .inr) (t + 1) (by omega_arith)
      with h' | h'
    · exact Or.inr (by dsimp only; omega_arith)
    · exact Or.inl h'
  · by_cases h6 : i = 83 ∧ c.n = 6
    · obtain ⟨rfl, h6⟩ := h6
      refine Or.inr ?_
      dsimp only
      rw [sl_eq' c 83, ix_83 c h6, bitsAt_eq]
      show 64 + 8 * c.n * 2 + 8 * c.n ≤ _
      have : 8 * c.n * 45 = 8 * c.n * 2 + 8 * c.n * 43 := by omega_arith
      omega_arith
    · exact Or.inl (bits_le_sl hj ht h (by
        by_cases e : i = 83
        · exact .inr fun h' => h6 ⟨e, h'⟩
        · exact .inl e))

theorem offset_eq (J : Nat) : WinCfg.offset J = 8 * geom J := by
  have := geom_mul J
  unfold WinCfg.offset
  omega_arith

/-- The recoded scalar below `2^b`: `k + 8 Σ_{j<J} 16^j < 16^J` for
`J = ⌈(b + 2) / 4⌉` (`Cfg.winJ`). -/
theorem recode_lt_bits {k b : Nat} (hk : k < 2 ^ b) :
    k + 8 * geom ((b + 5) / 4) < 16 ^ ((b + 5) / 4) := by
  obtain hg := geom_mul ((b + 5) / 4)
  obtain h4 : 2 ^ b * 4 ≤ 16 ^ ((b + 5) / 4) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul, show 2 ^ b * 4 = 2 ^ (b + 2) by rw [Nat.pow_add]]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  omega_arith

/-! ## `d` below `2^nbits` -/

theorem se_mask {m : Nat} (hm : m < 31) :
    (BitVec.ofNat 32 (2 ^ m - 1)).signExtend 64 = BitVec.ofNat 64 (2 ^ m - 1) := by
  obtain h : 2 ^ m - 1 < 2 ^ 31 := by
    have := Nat.pow_lt_pow_right (show 1 < 2 by decide) hm; omega_arith
  obtain hm' : (BitVec.ofNat 32 (2 ^ m - 1)).msb = false := by
    rw [BitVec.msb_eq_decide]; simp only [BitVec.toNat_ofNat, decide_eq_false_iff_not]; omega_arith
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm']
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega_arith

/-- `r8 = [d] mod 2^m`. -/
theorem movAnd_ok {s : State} {base : Addr} {size : Nat} (hs : Scr s base size) {d m : Nat}
    (hd : d + 8 ≤ size) (hm : m < 31) :
    WP isa (.block [.mov .r8 (.mem (sc d)), .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ m - 1)))]) s
      fun s' => (s'.gpr .r8).toNat = (word s.mem base d).toNat % 2 ^ m ∧ Keeps [.r8] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, exec, readSrc_sc hs hd, Option.map_some]
  simp only [execAlu, readSrc, Option.bind_some, runStep_some, runBlock_nil, RegUpd.gpr_setReg_self,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · have h64 : 2 ^ m - 1 < 2 ^ 64 := by
      have := Nat.pow_lt_pow_right (show 1 < 2 by decide) (show m < 64 by omega_arith); omega_arith
    rw [se_mask hm, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64,
      Nat.and_two_pow_sub_one_eq_mod]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr, ite_false]

theorem mask_arith {L B T m : Nat} (hL : L < B) :
    (L + B * T) % (B * 2 ^ m) = L + B * (T % 2 ^ m) := by
  obtain hT := Nat.div_add_mod T (2 ^ m)
  obtain hp : 0 < 2 ^ m := Nat.pow_pos (by decide)
  obtain hlt : L + B * (T % 2 ^ m) < B * 2 ^ m := by
    have := Nat.mod_lt T hp
    have : B * (T % 2 ^ m) + B ≤ B * 2 ^ m := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ this
    omega_arith
  rw [show L + B * T = L + B * (T % 2 ^ m) + B * 2 ^ m * (T / 2 ^ m) by
    conv_lhs => rw [← hT]
    rw [Nat.mul_add, Nat.mul_assoc]; omega_arith]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]

/-- ECDH's `d` at `K` reduced below `2^nbits` (`maskK`). -/
theorem maskK_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hk8 : sv c base s K < 2 ^ (8 * c.C.len)) :
    WP isa (.block (Impl.Ecdh.X86_64.Cfg.maskK c)) s fun s' => Scr s' base size ∧
      KeepRegs [.r8] s s' ∧ sv c base s' K = sv c base s K % 2 ^ c.nbits ∧
      Unch base (slW c [K]) s.mem s'.mem := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  unfold Impl.Ecdh.X86_64.Cfg.maskK
  split
  · rename_i hlt
    obtain ⟨hm1, hm2⟩ := hc.mask hlt
    obtain hK := sl_le c h7 (i := K) (by decide)
    obtain hd : c.sl K + 8 * (c.n - 1) + 8 ≤ size := by
      have : 8 * (c.n - 1) + 8 = 8 * c.n := by omega_arith
      omega_arith
    rw [show ([.mov .r8 (.mem (sc (c.sl K + 8 * (c.n - 1)))),
        .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ (c.nbits - 64 * (c.n - 1)) - 1))),
        .store (sc (c.sl K + 8 * (c.n - 1))) .r8] : List Instr) =
      [.mov .r8 (.mem (sc (c.sl K + 8 * (c.n - 1)))),
        .alu .and .r8 (.imm (BitVec.ofNat 32 (2 ^ (c.nbits - 64 * (c.n - 1)) - 1)))] ++
      ([.store (sc (c.sl K + 8 * (c.n - 1))) .r8] : List Instr) from rfl, WP.block_append_iff]
    refine WP.mono (movAnd_ok hs hd hm2) fun s₁ ⟨e₁, k₁⟩ => ?_
    obtain hs₁ := hs.of_keeps k₁ (by decide)
    refine WP.mono (storeX_ok hs₁ .r8 hd) fun s₂ ⟨m₂, g₂, _, _, rd₂, wr₂⟩ => ?_
    obtain hs₂ : Scr s₂ base size := ⟨by rw [g₂]; exact hs₁.rdi, by rw [wr₂]; exact hs₁.wr, hs₁.nowrap⟩
    obtain O₂ : Outside base (c.sl K + 8 * (c.n - 1)) 8 s.mem s₂.mem := by
      rw [m₂, k₁.2.1]; exact writeW_outside _ _ _ (by omega_arith)
    refine ⟨hs₂, ⟨fun r hr => by rw [g₂]; exact k₁.1 r hr, by rw [rd₂, k₁.2.2.1], by rw [wr₂, k₁.2.2.2]⟩,
      ?_, fun x hx => ?_⟩
    · -- The low words are kept, and the top word masked.
      obtain ⟨k, hk⟩ : ∃ k, c.n = k + 1 := ⟨c.n - 1, by omega_arith⟩
      simp only [sv]
      rw [hk, wordsVal_succ_top, wordsVal_succ_top, show k = c.n - 1 by omega_arith,
        O₂.wordsVal (by omega_arith) (by omega_arith), m₂, word_writeW_self]
      change _ + _ * (s₁.gpr .r8).toNat = _
      obtain hb : 2 ^ c.nbits = 2 ^ (64 * (c.n - 1)) * 2 ^ (c.nbits - 64 * (c.n - 1)) := by
        rw [← Nat.pow_add]; congr 1; omega_arith
      rw [e₁, hb, mask_arith (wordsVal_lt _ _ _ _)]
    · rw [O₂ x (by
        have := hx _ (List.mem_singleton_self _)
        dsimp only at this
        omega_arith)]
  · rename_i hlt
    obtain he : c.nbits = 8 * c.C.len := by have := hc.nbits_le; omega_arith
    refine WP.block_nil ⟨hs, ⟨fun _ _ => rfl, rfl, rfl⟩, ?_, Unch.refl _ _ _⟩
    rw [he, Nat.mod_eq_of_lt hk8]

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
theorem winMul_ok (hc : BaseCfgOk c) (hA : AM3 c.C) (h9 : c.n ≤ 9) (hC : Law c.C) {base : Addr} {s : State}
    (hs : Scr s base size) {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P) {ks : Nat} (hks : ks < 45)
    (hk8 : sv c base s ks < 2 ^ c.nbits) {rest : Prog isa} {R : State → Prop}
    (h : ∀ s', WinMulPost c base P (sv c base s ks) s s' → WP isa rest s' R) (hkT : ks ≠ TMP := by decide) :
    WP isa (.seq (.seq (c.winPrep (c.sl ks)) (WinCfg.window (winQ c)).inline) rest) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  have hp3 := hc.p_ge
  obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
  obtain hrec : wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ < 16 ^ c.winJ := recode_lt_bits hk8
  obtain hJle : c.winJ ≤ 16 * c.n + 1 := by
    unfold Cfg.winJ; have := hc.len_hi; have := hc.nbits_le; omega_arith
  obtain hWK : c.sl WK + 16 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WK + 1) (by decide)
    simp (disch := sl_ne) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega_arith
  obtain hKW := sl_lt c (show ks < WK by unfold WK; omega_arith) (.inl hkT)
  obtain h16 : (16 : Nat) ^ c.winJ ≤ 2 ^ (64 * (c.n + 1)) := by
    rw [show (16 : Nat) = 2 ^ 4 by rfl, ← Nat.pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega_arith)
  have hJ : (winQ c).J = c.winJ := rfl
  have hK : c.winK = c.sl WK := rfl
  have hB : c.winBits = c.sl WB := rfl
  obtain e82 : c.sl WK + 16 * c.n = c.sl WB := by simp (disch := sl_ne) only [sl_eq]; unfold WK WB; omega_arith
  obtain h4 := (hc.inv (by omega_arith)).1
  obtain hB8 : c.sl WB + 64 * (c.n + 1) ≤ c.sl WB + 80 * c.n := by omega_arith
  obtain hBs : c.sl WB + 80 * c.n ≤ size := by
    have := sl_le_win c h9 (i := WB + 9) (by decide)
    simp (disch := sl_ne) only [sl_eq] at this ⊢; rw [Nat.mul_add] at this; omega_arith
  rw [Cfg.winPrep]
  refine WP.seq (WP.seq (WP.seq ?_))
  rw [hK, offset_eq]
  refine WP.mono (addConst_ok hs (n := c.n) (src := c.sl ks) (dst := c.sl WK)
    (c := 8 * geom c.winJ) h0 (sl_le c h7 hks) (by omega_arith)
    (Or.inl (by omega_arith)) (by omega_arith) (by omega_arith)) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
  obtain hs₁ := hs.of_keepRegs k₁ (by decide)
  rw [hB]
  refine WP.mono (bits_ok hs₁ (n := c.n + 1) (src := c.sl WK) (dst := c.sl WB) (by omega_arith) (by omega_arith)
    (by omega_arith) (by omega_arith) (Or.inl (by omega_arith))) fun s₂ ⟨b₂, k₂, O₂⟩ => ?_
  obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
  rw [e₁] at b₂
  obtain U₂ : Unch base (winX c) s.mem s₂.mem :=
    ((O₁.mono (o' := c.sl WK) (n' := 16 * c.n) (Nat.le_refl _) (by omega_arith)).unch.trans
      ((O₂.mono (o' := c.sl WB) (n' := 80 * c.n) (Nat.le_refl _) (by omega_arith)).unch)).mono
      (by intro w hw; simpa [winX, hK, hB] using hw)
  obtain F₂ := F.unch h7 hn fixedOk_winX U₂
  obtain e₂ : ∀ {i}, i < 45 → sv c base s₂ i = sv c base s i := fun hi =>
    sv_unch U₂ h7 hn hi (apart_winX hi)
  obtain hM₂ := modP_of hc F₂.mp
  obtain tv : ∀ {i}, i < 45 → tmv c.C c.n base s₂ (c.sl i) = tmv c.C c.n base s (c.sl i) := fun hi => by
    show toM _ _ (sv c base s₂ _) = toM _ _ (sv c base s _); rw [e₂ hi]
  obtain hF : WinFixed (winQ c) c.C base s₂ P (wordsVal s.mem base (c.sl ks) c.n + 8 * geom c.winJ) := by
    refine ⟨?_, ?_, fun x hx => ?_, F₂.zero, ?_, fun t ht => ?_⟩
    · show toM _ _ (wordsVal s₂.mem _ (c.sl AP) c.n) = _; rw [F₂.ap]; exact toM_cmont hc _
    · show toM _ _ (sv c base s₂ BP) = _; rw [e₂ (by decide), hbp]; exact toM_cmont hc _
    · simp only [winRo, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
      · exact lt_of_eq_of_lt F₂.ap (hmont _)
      · exact lt_of_eq_of_lt ((e₂ (i := BP) (by decide)).trans hbp) (hmont _)
      · exact lt_of_eq_of_lt F₂.zero (by omega_arith)
      · exact lt_of_eq_of_lt (e₂ (i := PX) (by decide)) hpx
      · exact lt_of_eq_of_lt (e₂ (i := PY) (by decide)) hpy
      · exact lt_of_eq_of_lt F₂.onep (Nat.mod_lt _ (by omega_arith))
    · show Rep _ (tmv c.C c.n base s₂ (c.sl PX)) (tmv c.C c.n base s₂ (c.sl PY))
        (tmv c.C c.n base s₂ (c.sl ONEP)) P
      rw [tv (by decide), tv (by decide), tv (by decide)]; exact hrep
    · rw [hJ] at ht
      exact b₂ t (by omega_arith)
  refine WP.mono (window_ok (winLayQ hc h9) (winXQ hc h9) hpR hC hA hP hc.p_lt (hmont 1)
    (show toM c.C.p (2 ^ (64 * c.n)) (c.mont 1) = 1 by rw [toM_cmont hc]; rfl) hs₂ (hM₂.inl c.hot) hF
    (by rw [hJ]; exact hrec) (Nat.le_add_left _ _)) fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => h s₃ ?_
  rw [winW_eq] at U₃
  rw [hJ, Nat.add_sub_cancel] at R₃
  obtain c₁ : ∀ r ∈ [Reg.rax, .r8], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp [powClob, clob]
    · exact List.mem_cons_of_mem _ (r8_mem_clob _)
  obtain c₂ : ∀ r ∈ [Reg.rax, .rdx, .rbx], r ∈ powClob c.n := by
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [powClob, clob]
  exact ⟨hs₂.of_keepRegs K₃ (rdi_not_powClob _), ((k₁.mono c₁).trans (k₂.mono c₂)).trans K₃,
    U₂.trans U₃, M₃.of_inl, L₃, R₃⟩

/-! ## `[d]P`, by windows or the ladder, and `Z^(p-2)` -/

/-- What `mulQ` (the window method or the ladder) and the power may write. -/
def mulI : List Nat := otherI ++ tblI ++ [TMP] ++
  [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1, T2, T3, T4, T5, TX, TY, TZ, TMP, K]

theorem mulI_idx : ∀ i ∈ mulI, i = TMP ∨ 12 ≤ i := by decide

/-- A numbered slot below the tables not in `mulI`, apart from what it writes. -/
theorem apart_mulW {i : Nat} (hi : i < 45) (h₁ : i ∉ mulI) (h₂ : i ∉ [ACC, PT, TMP]) :
    ∀ w ∈ winX c ++ slW c mulI ++ pwW c ++ [(bitsAt c.n 0, 64 * c.n + 8)],
      c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_append (apart_append (apart_winX hi) (apart_slW h₁)) (apart_pwW hi h₂))
    fun w hw => by
      rw [List.mem_singleton.mp hw]
      exact Or.inl (sl_below_bits c hi 0 0 (.inl fun h => h₂ (by subst h; decide)))

theorem fixedOk_mulW : FixedOk c (winX c ++ slW c mulI ++ pwW c ++ [(bitsAt c.n 0, 64 * c.n + 8)]) :=
  ((fixedOk_winX.append (fixedOk_slW mulI_idx)).append fixedOk_pwW).append fun w hw => by
    rw [List.mem_singleton.mp hw]
    exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (i := 12) (by decide) 0 0))

theorem slW_mono {l l' : List Nat} (h : ∀ i ∈ l, i ∈ l') {w : Nat × Nat} (hw : w ∈ slW c l) :
    w ∈ slW c l' := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
  exact List.mem_map.mpr ⟨i, h i hi, rfl⟩

/-- What `mulQ` and the power may write. -/
abbrev mulQW' (c : Cfg) : List (Nat × Nat) := winX c ++ slW c mulI ++ pwW c ++ [(bitsAt c.n 0, 64 * c.n + 8)]

/-- What `mulQ` and the power leave: `R` represents `[k]P` (for `k < 2^nbits`;
for more words, any `k`). -/
structure MulPost (c : Cfg) (base : Addr) (P : Point c.C) (k : Nat) (s s' : State) : Prop where
  scr : Scr s' base size
  gpr : ∀ r, r ∉ invClob c.n → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  unch : Unch base (mulQW' c) s.mem s'.mem
  q : k < 2 ^ c.nbits → Rep c.C (tmv c.C c.n base s' (c.sl RX)) (tmv c.C c.n base s' (c.sl RY))
    (tmv c.C c.n base s' (c.sl RZ)) (mul k P)
  acc_lt : sv c base s' ACC < c.C.p
  acc : toM c.C.p (2 ^ (64 * c.n)) (sv c base s' ACC) = tmv c.C c.n base s' (c.sl RZ) ^ (c.C.p - 2)
  rz_lt : sv c base s' RZ < c.C.p

/-- `[k]P`, for `k` at `K` (and its bits in the first table), by windows for
up to nine words and by the ladder for more, then `Z^(p-2)`. -/
theorem mulPow_ok (hc : BaseCfgOk c) (hC : Law c.C) {base : Addr} {s : State} (hs : Scr s base size)
    {g : Reg → BitVec 64} (F : Fixed c base g s.mem) (hbp : sv c base s BP = c.mont c.C.b)
    {P : Point c.C} (hP : onCurve c.C P = true) (hpx : sv c base s PX < c.C.p) (hpy : sv c base s PY < c.C.p)
    (hrep : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY))
      (tmv c.C c.n base s (c.sl ONEP)) P)
    (hrx : sv c base s RX = 0) (hry : sv c base s RY = c.mont 1) (hrz : sv c base s RZ = 0)
    {k : Nat} (hk : sv c base s K = k) (hk8 : k < 2 ^ (8 * c.C.len))
    (ht₀ : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 0 + t)) = if k.testBit t then 1 else 0)
    (ht₁ : ¬ c.n ≤ 9 → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    (hm : c.mul.isSome = true → (c.n = 4 ∨ c.n = 6 ∨ c.n = 8) ∧ c.mulFn.noCalls = true)
    {rest : Prog isa} {R : State → Prop} (h : ∀ s', MulPost c base P k s s' → WP isa rest s' R) :
    WP isa (.seq (Impl.Ecdh.X86_64.Cfg.mulQ c).inline (.seq c.pPow.inline rest)) s R := by
  have h0 := hc.n0
  have h7 := hc.n10
  have hn := hs.nowrap
  obtain hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Impl.Ecdh.X86_64.Cfg.mulQ
  split
  · rename_i h9
    refine WP.seq (WP.seq (WP.mono (maskK_ok hc hs (hk ▸ hk8)) fun s₁ ⟨hs₁, k₁, e₁, U₁⟩ => ?_))
    obtain F₁ := F.unch h7 hn (fixedOk_slW (l := [K]) (by decide)) U₁
    obtain v₁ : ∀ {i}, i < 45 → i ≠ K → sv c base s₁ i = sv c base s i := fun hi hne =>
      sv_unch U₁ h7 hn hi (apart_slW (by simpa using hne))
    obtain tv₁ : ∀ {i}, i < 45 → i ≠ K → tmv c.C c.n base s₁ (c.sl i) = tmv c.C c.n base s (c.sl i) :=
      fun hi hne => by show toM _ _ (sv c base s₁ _) = toM _ _ (sv c base s _); rw [v₁ hi hne]
    refine WP.seq_iff.mp (winMul_ok hc (hc.window_am3 h9.2) h9.1 hC hs₁ F₁ (by rw [v₁ (by decide) (by decide)]; exact hbp) hP
      (by rw [v₁ (by decide) (by decide)]; exact hpx) (by rw [v₁ (by decide) (by decide)]; exact hpy)
      (by rw [tv₁ (by decide) (by decide), tv₁ (by decide) (by decide), tv₁ (by decide) (by decide)]; exact hrep)
      (ks := K) (by decide) (by rw [e₁]; exact Nat.mod_lt _ (Nat.pow_pos (by decide))) fun s₃ W => ?_)
    obtain F₃ := F₁.unch h7 hn (fixedOk_winX.append (fixedOk_slW (by decide))) W.unch
    obtain rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := W.lt _ (by simp)
    refine WP.seq (WP.mono (pPow_ok hc W.scr W.mod rz₃ F₃.onep (fun h9 t ht => by
        rw [tbl_unch W.unch h7 hn (j := 1) (by decide) ht (apart_append (tbl_apart_winX (by decide) ht)
          (tbl_apart_slW' (by decide) (by decide) ht)),
          tbl_unch U₁ h7 hn (j := 1) (by decide) ht (tbl_apart_slW' (by decide) (by decide) ht)]
        exact ht₁ h9 t ht)) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
    obtain r₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
      sv_unch U₄ h7 hn hi (apart_pwW hi h₁)
    refine ⟨W.scr.of_keepRegs K₄ (rdi_not_invClob _), fun r hr => ?_, by rw [K₄.rd, W.keep.rd, k₁.rd],
      by rw [K₄.wr, W.keep.wr, k₁.wr], ((U₁.trans W.unch).trans U₄).mono ?_, fun hlt => ?_, lt₄, ?_, ?_⟩
    · rw [K₄.gpr r hr, W.keep.gpr r (fun h => hr (List.mem_cons_of_mem _ h)),
        k₁.gpr r (fun h => hr (by
          rw [List.mem_singleton.mp h]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (r8_mem_clob _))))]
    · intro w hw
      refine List.mem_append_left _ ?_
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
  · cases hm₂ : c.mul with
    | none =>
      obtain hk' : k < 2 ^ (64 * c.n) := hk ▸ wordsVal_lt _ _ _ _
      obtain hstep := step_rep (L := Impl.Ecdh.X86_64.Cfg.ladderQ c) (k := k) hC hP
        (by
          show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl AP) c.n) = _
          rw [F.ap]; exact toM_cmont hc _)
        (by
          show toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem _ (c.sl B3P) c.n) = _
          rw [F.b3p]; exact toM_cmont hc _)
        hrep
      refine ladPow_ok hc hs F hstep (by rw [shiftRight_eq_zero hk', mul_zero_pt]; exact rep_infinity' hC)
        hpx hpy hrx hry hrz ht₀ ht₁ fun s₅ L => h s₅ ?_
      refine ⟨L.scr, L.gpr, L.rd, L.wr, L.unch.mono ?_, fun _ => by have := L.q; rwa [Nat.shiftRight_zero] at this,
        L.acc_lt, L.acc, L.rz_lt⟩
      intro w hw
      refine List.mem_append_left _ ?_
      simp only [mulI, slW, List.map_append, List.mem_append] at hw ⊢
      rcases hw with hw | hw
      · exact Or.inl (Or.inr (Or.inr (slW_mono (c := c) (l := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1,
          T2, T3, T4, T5, TX, TY, TZ, TMP]) (l' := [RX, RY, RZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, T0, T1,
          T2, T3, T4, T5, TX, TY, TZ, TMP, K]) (by decide) hw)))
      · exact Or.inr hw
    | some C =>
      obtain ⟨h4, hnc⟩ := hm (by rw [hm₂]; rfl)
      have hp3 := hc.p_ge
      obtain hmont : ∀ x, c.mont x < c.C.p := fun x => Nat.mod_lt _ (by omega_arith)
      obtain sz : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ size := fun hi => sl_le c h7 hi
      show WP isa (.seq (.seq (.block (copy c.n (c.sl RX) (c.sl PX) ++ copy c.n (c.sl RY) (c.sl PY))) c.mulFn)
        (.seq c.pPow.inline rest)) s R
      rw [← Code.inline_of_noCalls hnc]
      refine WP.seq (WP.seq ?_)
      rw [WP.block_append_iff]
      refine WP.mono (copy_ok (size := size) c.n hs (o := c.sl RX) (a := c.sl PX)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RX) (j := PX) (by decide) with h | h <;> omega_arith))
        fun s₁ ⟨v₁, k₁, O₁⟩ => ?_
      obtain hs₁ := hs.of_keepRegs k₁ (by decide)
      refine WP.mono (copy_ok (size := size) c.n hs₁ (o := c.sl RY) (a := c.sl PY)
        (sz (by decide)) (sz (by decide)) (by rcases sl_apart c (i := RY) (j := PY) (by decide) with h | h <;> omega_arith))
        fun s₂ ⟨v₂, k₂, O₂⟩ => ?_
      obtain hs₂ := hs₁.of_keepRegs k₂ (by decide)
      obtain U₂ : Unch base (slW c [RX, RY]) s.mem s₂.mem := O₁.unch.trans O₂.unch
      obtain e₂ := fun {i} (hi : i < 45) (hl : i ∉ [RX, RY]) => sv_unch U₂ h7 hn hi (apart_slW hl)
      have O₁' : Unch base (slW c [RX]) s.mem s₁.mem := O₁.unch
      have O₂' : Unch base (slW c [RY]) s₁.mem s₂.mem := O₂.unch
      obtain rx₂ : sv c base s₂ RX = sv c base s PX :=
        (sv_unch O₂' h7 hn (i := RX) (by decide) (apart_slW (by decide))).trans v₁
      obtain ry₂ : sv c base s₂ RY = sv c base s PY :=
        v₂.trans (sv_unch O₁' h7 hn (i := PY) (by decide) (apart_slW (by decide)))
      obtain hz : tmv c.C c.n base s (c.sl ONEP) = 1 := by
        change toM _ _ (wordsVal s.mem base (c.sl ONEP) c.n) = 1
        rw [F.onep]
        exact toM_one (unitMod_pow_two hc.p_odd _)
      obtain eP : ptQ c base s₂ = P := by
        show Point.affine (toM _ _ (sv c base s₂ RX)) (toM _ _ (sv c base s₂ RY)) = _
        obtain hrep₁ : Rep c.C (tmv c.C c.n base s (c.sl PX)) (tmv c.C c.n base s (c.sl PY)) 1 P := by
          rw [← hz]; exact hrep
        rw [rx₂, ry₂]; exact (Rep.eq_affine hC hrep₁).symm
      refine WP.mono (mulFn_ok hc h4 hC hs₂ ((e₂ (by decide) (by decide)).trans F.mp)
        ((e₂ (by decide) (by decide)).trans F.zero) ((e₂ (by decide) (by decide)).trans F.onep)
        ((e₂ (by decide) (by decide)).trans F.ap) ((e₂ (by decide) (by decide)).trans F.b3p)
        (by rw [rx₂]; exact hpx) (by rw [ry₂]; exact hpy) (by rw [eP]; exact hP))
        fun s₃ ⟨K₃, U₃, M₃, L₃, R₃⟩ => ?_
      obtain kk₂ : sv c base s₂ K = sv c base s K := e₂ (by decide) (by decide)
      rw [eP, kk₂, hk] at R₃
      obtain U₃' := U₂.trans U₃
      obtain one₃ : wordsVal s₃.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p :=
        (sv_unch U₃' h7 hn (i := ONEP) (by decide) (apart_append (apart_slW (by decide))
          (apart_append (apart_slW (by decide)) fun w hw => apart_bits_slW (i := ONEP) (l := []) (by decide)
            (by decide) w (List.mem_append_left _ hw)))).trans F.onep
      obtain rz₃ : wordsVal s₃.mem base (c.sl RZ) c.n < c.C.p := L₃ _ (by simp)
      refine WP.seq (WP.mono (pPow_ok hc (hs₂.of_keepRegs K₃ (rdi_not_powClob _)) M₃ rz₃ one₃
        (fun h9' => absurd (by omega_arith) h9')) fun s₄ ⟨K₄, U₄, lt₄, v₄⟩ => h s₄ ?_)
      obtain r₄ : ∀ {i}, i < 45 → i ∉ [ACC, PT, TMP] → sv c base s₄ i = sv c base s₃ i := fun hi h₁ =>
        sv_unch U₄ h7 hn hi (apart_pwW hi h₁)
      obtain hk₁ : ∀ r ∈ [Reg.rax], r ∈ powClob c.n := fun r hr => by
        simp only [List.mem_singleton] at hr; simp [hr, powClob, clob]
      obtain K₃' := ((k₁.mono hk₁).trans (k₂.mono hk₁)).trans K₃
      refine ⟨(hs₂.of_keepRegs K₃ (rdi_not_powClob _)).of_keepRegs K₄ (rdi_not_invClob _),
        fun r hr => ?_, by rw [K₄.rd, K₃'.rd], by rw [K₄.wr, K₃'.wr],
        (U₃'.trans U₄).cover (W' := mulQW' c) ?_, fun _ => ?_, lt₄, ?_, ?_⟩
      · rw [K₄.gpr r hr, K₃'.gpr r (fun h => hr (List.mem_cons_of_mem _ h))]
      · intro w hw
        refine ⟨w, ?_, Nat.le_refl _, Nat.le_refl _⟩
        obtain inI : w ∈ slW c mulI → w ∈ mulQW' c := fun h =>
          List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right (winX c) h))
        obtain inP : w ∈ pwW c → w ∈ mulQW' c := fun h => List.mem_append_left _ (List.mem_append_right _ h)
        rcases List.mem_append.mp hw with hw | hw
        · rcases List.mem_append.mp hw with hw | hw
          · exact inI (slW_mono (by decide) hw)
          · rcases List.mem_append.mp hw with hw | hw
            · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
              obtain key : ∀ i ∈ [RX, RY, RZ, ACC, PT, TX, TY, TZ, T0, T1, T2, T3, T4, T5, DX, DY, DZ, TMP],
                  i = ACC ∨ i ∈ mulI := by decide
              rcases key i hi with rfl | h
              · exact inP (List.mem_append_left _ (List.mem_map_of_mem (by decide)))
              · exact inI (List.mem_map_of_mem h)
            · exact List.mem_append_right _ hw
        · exact inP hw
      · show Rep _ (toM _ _ (sv c base s₄ RX)) (toM _ _ (sv c base s₄ RY)) (toM _ _ (sv c base s₄ RZ)) _
        rw [r₄ (i := RX) (by decide) (by decide), r₄ (i := RY) (by decide) (by decide),
          r₄ (i := RZ) (by decide) (by decide)]
        exact R₃
      · show _ = toM _ _ (sv c base s₄ RZ) ^ _
        rw [r₄ (i := RZ) (by decide) (by decide)]
        exact v₄
      · rw [r₄ (i := RZ) (by decide) (by decide)]; exact rz₃

end VG.Proof.Ecdh.X86_64
