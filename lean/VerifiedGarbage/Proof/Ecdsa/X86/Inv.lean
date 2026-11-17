module

public import VerifiedGarbage.Proof.Weierstrass.X86.Pow
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower
import VerifiedGarbage.Proof.Weierstrass.X86.P256Power
import VerifiedGarbage.Proof.Ecdsa.X86.Stages
import VerifiedGarbage.Proof.Ecdsa.X86.Lays
public import VerifiedGarbage.Proof.Ecdsa.X86.Fixed
import VerifiedGarbage.Proof.Weierstrass.X86.Fprog

/-! ### `Ecdsa.X86.InvLays`, which this module and modules that import it used -/

section

/-! # Working space for P-256 divstep inversion -/

@[expose] public section

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
    have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega_using [hn])
    simp only [sl_eq, wk_eq] at *
    omega_arith
  · exact (tbl_apart_wk hj ht) w hw

theorem flag_unch_pwW {l : List Nat} {base : Addr} {m m' : Mem} (hu : Unch base (pwW c l) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 32) (hl : FLAG ∉ l := by decide) :
    m'.readW (off base (c.sl FLAG)) 32 = m.readW (off base (c.sl FLAG)) 32 := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine Unch.readW32 hu (fun w hw => ?_) (by omega_using [hn, hF])
  rcases apart_pwW (c := c) (i := FLAG) (by decide) hl h7 w hw with h | h
  · exact Or.inl (by omega_using [h0, h])
  · exact Or.inr h

theorem invLay_of (hc : CfgOk c) (h4 : c.n = 4) {M : Mod} {F : Impl.Weierstrass.Mont.Modulus} (hMn : M.n = c.n)
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
  · exact ⟨hMn.trans h4, by simp only [InvCfg.ofMod, invAt_eq]; have := wk_own c (by omega_using [h4]); show _ ≤ 8192; omega_using [hinv, this],
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
    omega_using [hinv, this]

end VG.Proof.Ecdsa.X86

end

end

/-! # Field and scalar inversion through the shared divstep backend -/

@[expose] public section

namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv
variable {c : Cfg}

theorem invW_pwW {M : Mod} {F : Impl.Weierstrass.Mont.Modulus} (h4 : c.n = 4) (htmp : M.tmp = c.sl TMP)
    {base m : Nat} :
    ∀ w ∈ invW (InvCfg.ofMod M F (c.sl ACC) (c.sl base) (invAt c.n) m),
      ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [invW, InvCfg.ofMod, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(c.sl 45, 320), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(c.sl ACC, 8 * c.n), by simp, Nat.le_refl _, by simp only [h4]; omega_using []⟩
  · exact ⟨(c.sl TMP, 8 * c.n), by simp, by simp only [htmp]; exact Nat.le_refl _, by simp only [htmp, h4]; omega_using []⟩
  · exact ⟨(c.wk, 64 * c.n), by simp [wkW], by simp only [Cfg.wk, h4]; exact Nat.le_refl _,
      by simp only [Cfg.wk, h4]; omega_using []⟩
  · exact ⟨Mont.outW, by simp [wkW], Nat.le_refl _, Nat.le_refl _⟩

theorem powW_pwW {P : PowCfg} (h : powWx P c.wk = slW c [ACC, PT, TMP] ++ wkW c) :
    ∀ w ∈ powWx P c.wk, ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  rw [h] at hw
  rcases List.mem_append.mp hw with hw | hw
  · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨w, List.mem_append_right _ (List.mem_cons_of_mem _ hw), Nat.le_refl _, Nat.le_refl _⟩

theorem pPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p)
    (hO : wordsVal s.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0)
    (he : c.C.p - 2 < 2 ^ (64 * c.n)) :
    WP isa c.pPow s fun z => Keeps powClob s z ∧ Unch base (pwW c) s.mem z.mem ∧
      wordsVal z.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal z.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have hR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Cfg.pPow
  split
  · rename_i hfast
    have h4 := hfast.1
    obtain ⟨sound, ok⟩ := hc.inv_p hfast
    have H := sound (invLay_of hc h4 (M := c.MP') rfl (jm := MP) rfl (Or.inl rfl) rfl
      (base := RZ) (Or.inl rfl) c.C.p) (by have := hc.p_ge; omega_using [this])
      (by simpa only [h4] using hR) hs hM (by simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using hB) ok
    refine WP.mono H fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (invW_pwW h4 rfl), ?_, ?_⟩
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using lt
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using v
  · exact WP.mono (powField_ok (P := c.powP) (powLayP hc) (powWkP hc) hR hs hM hB hO hbits he)
      fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (powW_pwW (powWxP_eq c)), lt, v⟩

theorem nPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n)
    (hO : wordsVal s.mem base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0)
    (he : c.C.n - 2 < 2 ^ (64 * c.n)) :
    WP isa c.nPow s fun z => Keeps powClob s z ∧ Unch base (pwW c) s.mem z.mem ∧
      wordsVal z.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal z.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have hR := unitMod_pow_two hc.n_odd (64 * c.n)
  unfold Cfg.nPow
  split
  · rename_i hfast
    have h4 := hfast.1
    obtain ⟨sound, ok⟩ := hc.inv_n hfast
    have H := sound (invLay_of hc h4 (M := c.MN') rfl (jm := MN) rfl (Or.inr rfl) rfl
      (base := KM) (Or.inr rfl) c.C.n) (by have := hc.n_ge; omega_using [this])
      (by simpa only [h4] using hR) hs hM (by simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using hB) ok
    refine WP.mono H fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (invW_pwW h4 rfl), ?_, ?_⟩
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using lt
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using v
  · exact WP.mono (powScalar_ok (P := c.powN) (powLayN hc) (powWkN hc) hR hs hM hB hO hbits he)
      fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (powW_pwW (powWxN_eq c)), lt, v⟩

end VG.Proof.Ecdsa.X86
