module
public import VerifiedGarbage.Proof.Ecdsa.AArch64.Layout
import VerifiedGarbage.Proof.Framework.Taint


/-!
# ECDSA on AArch64: where the powers' slots are

The slots of the inversions `c.invP`, `c.invN` and of the power `c.powN` are
numbered slots `c.sl i` for distinct `i`, and their working slots are past
them (`CT`), so they are apart as `chainPow_ok` and `InvSound` need
(`invLayP`, `invLayN`, `chainLayN`): each fact is one about the numbers `i`,
which `decide` checks.
-/

@[expose] public section

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `x` and `y`, `k` and `k'` bytes long, are apart. -/
abbrev Apart (x k y k' : Nat) : Prop := x + k ≤ y ∨ y + k' ≤ x

/-- Slots away from where the temporary area may be (`sl_apart`). -/
abbrev Away (l : List Nat) : Prop := ∀ i ∈ l, i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} (hi : i ≠ 54 ∧ i ≠ 61 ∧ i ≠ 82) (hl : Away l) :
    c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e (.inr hi) (.inr (hl j hj)) ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂)
    (h₁ : Away l₁ := by decide) (h₂ : Away l₂ := by decide) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn (h₁ i hi) h₂).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) (hl : Away l := by decide) :
    (l.map c.sl).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact h.imp_of_mem fun ha hb hab e => hab (sl_inj c hn e (.inr (hl _ hb)) (.inr (hl _ ha)))

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : BaseCfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n10 (hl i hi).1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hy
    have := (hl i hi).1
    have := (hl j hj).1
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := (hl i hi).1
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have := (hl i hi).1
    have := (hl i hi).2.2
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

/-- A numbered slot below the tables is apart from them. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat) (hiT : i ≠ TMP := by sl_ne) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  have := sl_lt c hi hiT
  rw [sl_eq c 45] at this
  rw [bitsAt_eq]
  omega

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) (hlw : Away lw := by decide) (hlr : Away lr := by decide) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd hlw, by rw [hw, hr]; exact map_sl_disj hn hd hlr hlw⟩

/-- The powers' table is in the working space, past the other slots. -/
theorem ct_le (c : Cfg) (h7 : c.n < 10) : c.sl CT + 9 * (8 * c.n) ≤ size := by
  simp (disch := decide) only [sl_eq]; unfold CT
  have : 8 * c.n * 69 ≤ 8 * 9 * 69 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- The powers' table is apart from the temporary area. -/
theorem ct_tmp (c : Cfg) : c.sl CT + 9 * (8 * c.n) ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ c.sl CT := by
  rw [sl_eq c CT]
  by_cases hr : c.n = 6 ∨ c.n = 8 ∨ c.n = 9
  · rw [sl_tmp c hr]; simp only [Mont.moAt, CT]
    rcases hr with h | h | h <;> rw [h] <;> omega
  · rw [sl_aff c hr]; simp only [TMP, CT]; right
    have : 8 * c.n * 2 + 8 * c.n ≤ 8 * c.n * 69 := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by decide)
    omega

/-! ## The powers' working slots and temporary area -/

theorem invTbl_none (h : c.inverse = none) : c.invTbl = c.sl CT := by simp only [Cfg.invTbl, h]
theorem invTmp_none (h : c.inverse = none) : c.invTmp = c.sl TMP := by simp only [Cfg.invTmp, h]

theorem invTbl_ge (hc : BaseCfgOk c) : c.sl CT ≤ c.invTbl := by
  rcases hc.inv_at with h | h
  · rw [invTbl_none h]
  · exact h.1

theorem invTbl_le (hc : BaseCfgOk c) : c.invTbl + 9 * (8 * c.n) ≤ size := by
  rcases hc.inv_at with h | h
  · rw [invTbl_none h]; exact ct_le c hc.n10
  · have := h.2.2.1; omega

theorem invSaveLen_le (c : Cfg) : c.invSaveLen ≤ 48 := by
  unfold Cfg.invSaveLen Cfg.invKept Cfg.invRegs
  split <;> simp

theorem invTbl_le8 (hc : BaseCfgOk c) : c.invTbl + (9 * (8 * c.n) + c.invSaveLen) ≤ size := by
  rcases hc.inv_at with h | h
  · rw [invTbl_none h, sl_eq c CT]
    have := hc.n10
    have := invSaveLen_le c
    show 64 + 8 * c.n * 69 + (9 * (8 * c.n) + c.invSaveLen) ≤ 8192
    omega
  · have := h.2.2.1; omega

theorem invTmp_ge64 (hc : BaseCfgOk c) : 64 ≤ c.invTmp := by
  rcases hc.inv_at with h | h
  · rw [invTmp_none h]; exact sl_ge64 c _
  · rcases h.2.2.2 with h' | h'
    · rw [h'.1]; exact Nat.le_add_right _ _
    · have := sl_ge64 c CT
      have := sl_ge64 c nslots
      omega

theorem invTbl8 (hc : BaseCfgOk c) : c.invTbl % 8 = 0 := by
  rcases hc.inv_at with h | h
  · rw [invTbl_none h]; exact sl_mod8 c _
  · exact h.2.1

theorem invTmp8 (hc : BaseCfgOk c) : c.invTmp % 8 = 0 := by
  rcases hc.inv_at with h | h
  · rw [invTmp_none h]; exact sl_mod8 c _
  · rcases h.2.2.2 with h' | h'
    · rw [h'.1]; simp only [slot, Nat.mul_assoc]; omega
    · exact h'.2.2.1

theorem invTmp_le (hc : BaseCfgOk c) : c.invTmp + 8 * c.n ≤ size := by
  rcases hc.inv_at with h | h
  · rw [invTmp_none h]; exact sl_le c hc.n10 (by decide)
  · rcases h.2.2.2 with h' | h'
    · rw [h'.1]; have := hc.n10; simp only [slot, TMP, size]; omega
    · exact h'.2.1

theorem invTbl_tmp (hc : BaseCfgOk c) :
    c.invTbl + 9 * (8 * c.n) ≤ c.invTmp ∨ c.invTmp + 8 * c.n ≤ c.invTbl := by
  rcases hc.inv_at with h | h
  · rw [invTbl_none h, invTmp_none h]; exact ct_tmp c
  · rcases h.2.2.2 with h' | h'
    · exact Or.inr (by omega)
    · rcases h'.1 with h'' | h''
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)

/-- A numbered slot below the tables is below the powers' working slots. -/
theorem sl_invTbl (hc : BaseCfgOk c) {i : Nat} (hi : i < 45) (hT : i ≠ TMP) :
    c.sl i + 8 * c.n ≤ c.invTbl :=
  Nat.le_trans (sl_lt c (show i < CT by unfold CT; omega) hT) (invTbl_ge hc)

/-- A numbered slot below the tables, but `TMP`, is apart from the powers'
temporary area. -/
theorem sl_invTmp (hc : BaseCfgOk c) {i : Nat} (hi : i < 45) (hT : i ≠ TMP) :
    c.sl i + 8 * c.n ≤ c.invTmp ∨ c.invTmp + 8 * c.n ≤ c.sl i := by
  rcases hc.inv_at with h | h
  · rw [invTmp_none h]; exact sl_apart c hT
  · rcases h.2.2.2 with h' | h'
    · rw [h'.1]; exact sl_apart_raw_tmp c hT
    · rcases h'.1 with h'' | h''
      · have := sl_invTbl hc hi hT
        exact Or.inl (by omega)
      · have := sl_lt c (j := nslots) (by unfold nslots; omega) hT (by decide)
        exact Or.inl (by omega)

theorem invMP_A (hc : BaseCfgOk c) : ModA { c.MP' with tmp := c.invTmp } := ⟨sl_mod8 c MP, invTmp8 hc⟩
theorem invMN_A (hc : BaseCfgOk c) : ModA { c.MN' with tmp := c.invTmp } := ⟨sl_mod8 c MN, invTmp8 hc⟩

/-- A power by a chain with its result in `ACC`, its base in slot `b` and its
table and temporary area the powers' (`invTbl`, `invTmp`). -/
theorem chainLay_of (hc : BaseCfgOk c) {P : ChainCfg} (hn : P.M.n = c.n) (hacc : P.acc = c.sl ACC)
    (htbl : P.tbl = c.invTbl) {b jm : Nat} (hb : P.base = c.sl b) (hmo : P.M.mo = c.sl jm)
    (htmp : P.M.tmp = c.invTmp) (hA : ModA P.M) (hb45 : b < 45) (hbs : b ∉ [ACC, TMP, jm])
    (hjm : jm < 45 ∧ jm ∉ [ACC, TMP]) : ChainLay P size := by
  have h0 := hc.n0
  have h7 := hc.n10
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbs hjm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hn, hacc, htbl, hb, hmo, htmp]
  · exact sl_le c h7 (by decide)
  · exact sl_le c h7 hb45
  · exact invTbl_le hc
  · exact sl_mod8 c _
  · exact sl_mod8 c _
  · exact invTbl8 hc
  · exact sl_apart c (Ne.symm hbs.1)
  · exact Or.inl (sl_invTbl hc (by decide) (by decide))
  · exact Or.inl (sl_invTbl hc hb45 hbs.2.1)
  · exact sl_invTmp hc (by decide) (by decide)
  · exact sl_invTmp hc hb45 hbs.2.1
  · exact invTbl_tmp hc
  · intro w hw
    simp only [chainW, hn, hacc, htbl, htmp, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hjm.2.1
    · exact Or.inl (sl_invTbl hc hjm.1 hjm.2.2)
    · exact sl_invTmp hc hjm.1 hjm.2.2
  · exact sl_apart c hbs.2.2

theorem invLayP (hc : BaseCfgOk c) : InvLay c.invP size :=
  InvLay.of_chain (chainLay_of hc (P := c.invP.toChain) rfl rfl rfl (b := RZ) (jm := MP) rfl rfl rfl (invMP_A hc)
    (by decide) (by decide) (by decide)) hc.n4 hc.n10

theorem invLayN (hc : BaseCfgOk c) : InvLay c.invN size :=
  InvLay.of_chain (chainLay_of hc (P := c.invN.toChain) rfl rfl rfl (b := KM) (jm := MN) rfl rfl rfl (invMN_A hc)
    (by decide) (by decide) (by decide)) hc.n4 hc.n10

theorem chainLayN (hc : BaseCfgOk c) : ChainLay c.powN size :=
  chainLay_of hc rfl rfl rfl (b := KM) (jm := MN) rfl rfl rfl (invMN_A hc) (by decide) (by decide)
    (by decide)

theorem chainOkN (hc : BaseCfgOk c) (h : c.fastN = false) : ChainOk c.powN (c.C.n - 2) :=
  ChainOk.of_check (hc.chain_n h)

end VG.Proof.Ecdsa.AArch64
