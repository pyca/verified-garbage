import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Stages

/-! # Working space for P-256 divstep inversion -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv
variable {c : Cfg}

abbrev pwW (c : Cfg) (l : List Nat := [ACC, PT, TMP]) : List (Nat × Nat) := slW c l ++ [(c.wk, 388)]

theorem apart_pwW {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) :
    ∀ w ∈ pwW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  refine apart_append (apart_slW hl) ?_
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_wk c hi)

theorem fixedOk_pwW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i := by decide) : FixedOk c (pwW c l) := by
  refine (fixedOk_slW hl).append ?_
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_wk c (i := 12) (by decide)))

theorem tbl_apart_pwW {l : List Nat} {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hl : ∀ i ∈ l, i < 45 := by decide) :
    ∀ w ∈ pwW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  refine apart_append (tbl_apart_slW hl j t) ?_
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (by have := bitsAt_below_wk c hj; omega)

theorem pwW_le (h7 : c.n < 10) (l : List Nat := [ACC, PT, TMP]) (hl : ∀ i ∈ l, i < 45 := by decide) : ∀ w ∈ pwW c l, w.1 + w.2 ≤ size := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact sl_le c h7 (hl i hi)
  · rw [List.mem_singleton.mp hw]
    simp only [wk_eq]
    show _ ≤ 8192
    have := Nat.mul_le_mul_left 360 (show c.n ≤ 9 by omega)
    omega

theorem flag_unch_pwW {l : List Nat} {base : Addr} {m m' : Mem} (hu : Unch base (pwW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l := by decide) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases apart_pwW (c := c) (i := FLAG) (by decide) hl w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem invLay_of (hc : CfgOk c) (h4 : c.n = 4) {M : Mod} (hMn : M.n = c.n)
    {jm : Nat} (hmo : M.mo = c.sl jm) (hjm : jm = MP ∨ jm = MN) (htmp : M.tmp = c.sl TMP)
    {base : Nat} (hb : base = RZ ∨ base = KM) (m : Nat) :
    InvLay (InvCfg.ofMod M c.wk (c.sl ACC) (c.sl base) (c.wk + 68) m) size := by
  have hjm45 : jm < 45 := by rcases hjm with rfl | rfl <;> decide
  have hb45 : base < 45 := by rcases hb with rfl | rfl <;> decide
  have below : ∀ {i}, i < 45 → c.sl i + 32 ≤ c.wk := by
    intro i hi
    simpa only [h4] using sl_below_wk c hi
  have bound : c.wk + 388 ≤ size := by rw [wk_eq, h4]; decide
  have hjT : jm ≠ TMP := by rcases hjm with rfl | rfl <;> decide
  have modTmp := sl_apart c hjT
  have outTmp := sl_apart c (show ACC ≠ TMP by decide)
  simp only [h4] at modTmp outTmp
  constructor
  · exact ⟨hMn.trans h4, bound, by simpa only [InvCfg.ofMod, hmo, h4] using sl_le c hc.n10 hjm45,
      by simpa only [InvCfg.ofMod, htmp, h4] using sl_le c hc.n10 (i := TMP) (by decide),
      Or.inr (by simpa only [InvCfg.ofMod, hmo] using Nat.le_trans (below hjm45) (Nat.le_add_right _ 68)),
      Or.inr (by simpa only [InvCfg.ofMod, htmp] using Nat.le_trans (below (i := TMP) (by decide)) (Nat.le_add_right _ 68)),
      by simpa only [InvCfg.ofMod, hmo, htmp] using modTmp⟩
  · simpa only [InvCfg.ofMod, h4] using sl_le c hc.n10 hb45
  · exact Or.inl (Nat.le_trans (below hb45) (Nat.le_add_right _ 68))
  · simpa only [InvCfg.ofMod, h4] using sl_le c hc.n10 (i := ACC) (by decide)
  · simpa only [InvCfg.ofMod, htmp] using outTmp
  · change c.wk + 68 ≤ size; omega
  · exact Or.inl (Nat.le_refl _)
  · exact Or.inr (below (by decide))
  · simpa only [InvCfg.ofMod, hmo] using Or.inr (a := c.wk + 68 ≤ c.sl jm) (below hjm45)
  · simpa only [InvCfg.ofMod, htmp] using Or.inr (a := c.wk + 68 ≤ c.sl TMP) (below (i := TMP) (by decide))

end VG.Proof.Ecdsa.X86
