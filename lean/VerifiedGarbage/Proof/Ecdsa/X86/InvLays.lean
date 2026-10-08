import VerifiedGarbage.Proof.Ecdsa.X86.Lays
import VerifiedGarbage.Proof.Ecdsa.X86.Stages

/-! # Working space for P-256 divstep inversion -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv
variable {c : Cfg}

/-- What the powers and the inversions write: their slots, the inversions'
table at `invAt` (320 bytes after the slots), and `wkW`. -/
abbrev pwW (c : Cfg) (l : List Nat := [ACC, PT, TMP]) : List (Nat × Nat) :=
  slW c l ++ (c.sl 45, 320) :: wkW c

theorem invAt_eq (c : Cfg) : invAt c.n = c.sl 45 := rfl

/-- The inversions' table is below the field arithmetic's own working space,
for `n = 4` (where the code inverts by divsteps). -/
theorem inv_below_wk (c : Cfg) (h4 : c.n = 4) : c.sl 45 + 320 ≤ c.wk := by
  rw [sl_eq, wk_eq, h4]; decide

theorem apart_pwW {l : List Nat} {i : Nat} (hi : i < 45) (hl : i ∉ l) (hn : c.n < 10 := by n10) :
    ∀ w ∈ pwW c l, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact apart_slW hl w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact Or.inl (sl_lt c hi)
  · exact (apart_wk hi) w hw

theorem fixedOk_pwW {l : List Nat} (hl : ∀ i ∈ l, i = TMP ∨ 12 ≤ i := by decide) (hn : c.n < 10 := by n10) :
    FixedOk c (pwW c l) := by
  refine (fixedOk_slW hl).append ?_
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_lt c (i := 12) (by decide)))
  · exact (fixedOk_wk) w hw

theorem tbl_apart_pwW {l : List Nat} {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hl : ∀ i ∈ l, i < 45 := by decide)
    (hn : c.n < 10 := by n10) :
    ∀ w ∈ pwW c l, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rcases List.mem_append.mp hw with hw | hw
  · exact (tbl_apart_slW hl j t) w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · refine Or.inr ?_
    have := wk_below_bits c j
    have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
    simp only [sl_eq, wk_eq] at *
    omega
  · exact (tbl_apart_wk hj ht) w hw

theorem flag_unch_pwW {l : List Nat} {base : Addr} {m m' : Mem} (hu : Unch base (pwW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l := by decide) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega)
  rcases apart_pwW (c := c) (i := FLAG) (by decide) hl h7 w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

theorem invLay_of (hc : CfgOk c) (h4 : c.n = 4) {M : Mod} {F : Spec.Weierstrass.Mont.Modulus} (hMn : M.n = c.n)
    {jm : Nat} (hmo : M.mo = c.sl jm) (hjm : jm = MP ∨ jm = MN) (htmp : M.tmp = c.sl TMP)
    {base : Nat} (hb : base = RZ ∨ base = KM) (m : Nat) :
    InvLay (InvCfg.ofMod M F (c.sl ACC) (c.sl base) (invAt c.n) m) size := by
  have hjm45 : jm < 45 := by rcases hjm with rfl | rfl <;> decide
  have hb45 : base < 45 := by rcases hb with rfl | rfl <;> decide
  have hinv := inv_below_wk c h4
  have hwk : c.wk = Mont.own 4 := by simp only [Cfg.wk, h4]
  have hjT : jm ≠ TMP := by rcases hjm with rfl | rfl <;> decide
  have modTmp := sl_apart c hjT
  have outTmp := sl_apart c (show ACC ≠ TMP by decide)
  have lt45 : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ c.sl 45 := fun hi => sl_lt c hi
  simp only [h4] at modTmp outTmp lt45
  constructor
  · exact ⟨hMn.trans h4, by simp only [InvCfg.ofMod, invAt_eq]; have := wk_own c (by omega); show _ ≤ 8192; omega,
      by simpa only [InvCfg.ofMod, hmo, h4] using sl_le c hc.n10 hjm45,
      by simpa only [InvCfg.ofMod, htmp, h4] using sl_le c hc.n10 (i := TMP) (by decide),
      Or.inr (by simpa only [InvCfg.ofMod, hmo, invAt_eq] using lt45 hjm45),
      Or.inr (by simpa only [InvCfg.ofMod, htmp, invAt_eq] using lt45 (i := TMP) (by decide)),
      by simpa only [InvCfg.ofMod, hmo, htmp] using modTmp⟩
  · simpa only [InvCfg.ofMod, h4] using sl_le c hc.n10 hb45
  · exact Or.inl (by simpa only [InvCfg.ofMod, invAt_eq] using lt45 hb45)
  · simpa only [InvCfg.ofMod, h4] using sl_le c hc.n10 (i := ACC) (by decide)
  · simpa only [InvCfg.ofMod, htmp] using outTmp
  · rfl
  · simp only [InvCfg.ofMod, invAt_eq, ← hwk]; exact hinv
  · simp only [InvCfg.ofMod, ← hwk]
    have := lt45 (i := ACC) (by decide)
    omega

end VG.Proof.Ecdsa.X86
