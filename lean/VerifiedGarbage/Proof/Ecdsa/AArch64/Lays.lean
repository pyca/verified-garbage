import VerifiedGarbage.Proof.Ecdsa.AArch64.SlotOps

/-!
# ECDSA on AArch64: where the powers' slots are

The slots of the inversions `c.invP`, `c.invN` and of the power `c.powN` are
numbered slots `c.sl i` for distinct `i`, and their working slots are past
them (`CT`), so they are apart as `chainPow_ok` and `InvSound` need
(`invLayP`, `invLayN`, `chainLayN`): each fact is one about the numbers `i`,
which `decide` checks.
-/

namespace VG.Proof.Ecdsa.AArch64

open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.AArch64
open VG.Proof.Mont.AArch64 VG.Proof.Mont VG.Proof.Weierstrass.AArch64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- `x` and `y`, `k` and `k'` bytes long, are apart. -/
abbrev Apart (x k y k' : Nat) : Prop := x + k ≤ y ∨ y + k' ≤ x

theorem sl_mem_map (hn : 0 < c.n) {i : Nat} {l : List Nat} : c.sl i ∈ l.map c.sl ↔ i ∈ l := by
  constructor
  · intro h
    obtain ⟨j, hj, e⟩ := List.mem_map.mp h
    exact sl_inj c hn e ▸ hj
  · exact List.mem_map_of_mem

theorem map_sl_disj (hn : 0 < c.n) {l₁ l₂ : List Nat} (h : ∀ i ∈ l₁, i ∉ l₂) :
    ∀ x ∈ l₁.map c.sl, x ∉ l₂.map c.sl := by
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  exact h i hi ((sl_mem_map hn).mp hx')

theorem map_sl_nodup (hn : 0 < c.n) {l : List Nat} (h : l.Nodup) : (l.map c.sl).Nodup :=
  List.Pairwise.map c.sl (fun _ _ hab e => hab (sl_inj c hn e)) h

/-- Numbered slots, apart from the modulus's and the temporary area. -/
theorem lay_map (hc : CfgOk c) {M : Mod} (hmo : M.mo = c.sl MP) (htmp : M.tmp = c.sl TMP)
    (hMn : M.n = c.n) {l : List Nat} (hl : ∀ i ∈ l, i < 45 ∧ i ≠ MP ∧ i ≠ TMP) :
    Lay M size (· ∈ l.map c.sl) := by
  have hn := hc.n0
  refine ⟨fun x hx => ?_, fun x y hx hy hxy => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn]; exact sl_le c hc.n7 (hl i hi).1
  · obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    rw [hMn]; exact sl_apart c fun h => hxy (h ▸ rfl)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, hmo]; exact sl_apart c (hl i hi).2.1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    rw [hMn, htmp]; exact sl_apart c (hl i hi).2.2

/-- A numbered slot below the tables is apart from them. -/
theorem sl_below_bits (c : Cfg) {i : Nat} (hi : i < 45) (j t : Nat) :
    c.sl i + 8 * c.n ≤ bitsAt c.n j + t := by
  have := sl_lt c hi
  rw [sl_eq c 45] at this
  rw [bitsAt_eq]
  omega

theorem rcbApart_of (hn : 0 < c.n) {S : RcbSlots} {p q o : Pt} {lw lr : List Nat}
    (hw : rcbW S o = lw.map c.sl) (hr : rcbR S p q = lr.map c.sl) (hnd : lw.Nodup)
    (hd : ∀ i ∈ lr, i ∉ lw) : RcbApart S p q o :=
  ⟨hw ▸ map_sl_nodup hn hnd, by rw [hw, hr]; exact map_sl_disj hn hd⟩

/-- The powers' table is in the working space, past the other slots. -/
theorem ct_le (c : Cfg) (h7 : c.n < 7) : c.sl CT + 9 * (8 * c.n) ≤ size := by
  rw [sl_eq]; unfold CT
  have : 8 * c.n * 69 ≤ 8 * 6 * 69 := Nat.mul_le_mul_right _ (by omega)
  show _ ≤ 8192
  omega

/-- A power by a chain with its result in `ACC`, its base in slot `b` and its
table at `CT`. -/
theorem chainLay_of (hc : CfgOk c) {P : ChainCfg} (hn : P.M.n = c.n) (hacc : P.acc = c.sl ACC)
    (htbl : P.tbl = c.sl CT) {b jm : Nat} (hb : P.base = c.sl b) (hmo : P.M.mo = c.sl jm)
    (htmp : P.M.tmp = c.sl TMP) (hA : ModA P.M) (hb45 : b < 45) (hbs : b ∉ [ACC, TMP, jm])
    (hjm : jm < 45 ∧ jm ∉ [ACC, TMP]) : ChainLay P size := by
  have h0 := hc.n0
  have h7 := hc.n7
  have lt : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ c.sl CT := fun hi => sl_lt c (by unfold CT; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbs hjm
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, hA, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hn, hacc, htbl, hb, hmo, htmp]
  · exact sl_le c h7 (by decide)
  · exact sl_le c h7 hb45
  · exact ct_le c h7
  · exact sl_mod8 c _
  · exact sl_mod8 c _
  · exact sl_mod8 c _
  · exact sl_apart c (Ne.symm hbs.1)
  · exact Or.inl (lt (by decide))
  · exact Or.inl (lt hb45)
  · exact sl_apart c (by decide)
  · exact sl_apart c hbs.2.1
  · exact Or.inr (lt (by decide))
  · intro w hw
    simp only [chainW, hn, hacc, htbl, htmp, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact sl_apart c hjm.2.1
    · exact Or.inl (lt hjm.1)
    · exact sl_apart c hjm.2.2
  · exact sl_apart c hbs.2.2

theorem invLayP (hc : CfgOk c) : InvLay c.invP size :=
  InvLay.of_chain (chainLay_of hc (P := c.invP.toChain) rfl rfl rfl (b := RZ) (jm := MP) rfl rfl rfl (MP'_A c)
    (by decide) (by decide) (by decide)) hc.n4 hc.n7

theorem invLayN (hc : CfgOk c) : InvLay c.invN size :=
  InvLay.of_chain (chainLay_of hc (P := c.invN.toChain) rfl rfl rfl (b := KM) (jm := MN) rfl rfl rfl (MN'_A c)
    (by decide) (by decide) (by decide)) hc.n4 hc.n7

theorem chainLayN (hc : CfgOk c) : ChainLay c.powN size :=
  chainLay_of hc rfl rfl rfl (b := KM) (jm := MN) rfl rfl rfl (MN'_A c) (by decide) (by decide)
    (by decide)

theorem chainOkN (hc : CfgOk c) (h : c.fastN = false) : ChainOk c.powN (c.C.n - 2) :=
  ChainOk.of_check (hc.chain_n h)

end VG.Proof.Ecdsa.AArch64
