import VerifiedGarbage.Proof.Ecdsa.X86_64.Lays
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages

/-!
# ECDSA on x86-64: `Z^(p-2)` and `k^(n-2)`

`Cfg.pPow` and `Cfg.nPow` are inverses by divsteps for a curve of up to nine
words (`InvSound`; `nPow` if `fastN`), else powers (`pow_ok`); either leaves `[ACC]` reading as
`[base]^(m - 2)` in Montgomery form, and writes only the slots and the
working area of `pwW` (`pPow_ok`, `nPow_ok`).
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

/-- What the powers may write: their slots, and the inversions' working area
past the tables of bits. -/
abbrev pwW (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, PT, TMP] ++ [(bitsAt c.n 3, 64 * c.n + 64)]

theorem rdi_not_invClob (n : Nat) : Reg.rdi ∉ invClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (rdi_not_powClob n)

theorem rsi_not_invClob (n : Nat) : Reg.rsi ∉ invClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (rsi_not_powClob n)

/-- A slot is apart from the inversions' working area. -/
theorem apart_pwA {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 3, 64 * c.n + 64)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  exact Or.inl (sl_below_bits c hi 3 0)

/-- A slot apart from what the powers write. -/
theorem apart_pwW {i : Nat} (hi : i < 45) (hl : i ∉ [ACC, PT, TMP]) :
    ∀ w ∈ pwW c, c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i :=
  apart_append (apart_slW hl) (apart_pwA hi)

theorem fixedOk_pwW : FixedOk c (pwW c) := by
  refine FixedOk.append (fixedOk_slW (by decide)) fun w hw => ?_
  rw [List.mem_singleton.mp hw]
  exact Or.inr (Nat.le_trans (Nat.le_add_right _ _) (sl_below_bits c (by decide) 3 0))

/-- The tables of bits are apart from the inversions' working area. -/
theorem tbl_apart_pwA {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) :
    ∀ w ∈ [(bitsAt c.n 3, 64 * c.n + 64)], bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  simp only [bitsAt_eq]
  have : (64 * c.n + 8) * j + 64 * c.n + 8 ≤ (64 * c.n + 8) * 3 := by
    have := Nat.mul_le_mul_left (64 * c.n + 8) (show j + 1 ≤ 3 by omega)
    rw [Nat.mul_succ] at this; omega
  exact Or.inl (by omega)

/-- The inversions' working area is in the working space. -/
theorem pwA_le (h7 : c.n < 10) : bitsAt c.n 3 + (64 * c.n + 64) ≤ size := by
  simp only [bitsAt_eq]; show _ ≤ 8192
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The flag word apart from what changed. -/
theorem flag_unch_of {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases hW w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- The tables of bits are apart from what the powers write. -/
theorem tbl_apart_pwW {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) :
    ∀ w ∈ pwW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW (by decide) j t) (tbl_apart_pwA hj ht)

/-- The flag word apart from what the powers write. -/
theorem flag_unch_pwW {base : Addr} {m m' : Mem} (hu : Unch base (pwW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega)
  rcases apart_pwW (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega)
  · exact Or.inr h

/-- The inversions' slots and working area, for up to nine words. -/
theorem invLay_of (hc : CfgOk c) (h6 : c.n ≤ 9) (h4 : 4 ≤ c.n) {M : Mod} (hMn : M.n = c.n) {jm : Nat}
    (hmo : M.mo = c.sl jm) (hjm : jm = MP ∨ jm = MN) (htmp : M.tmp = c.sl TMP) {base : Nat}
    (hb : base = RZ ∨ base = KM) (m : Nat) :
    InvLay (InvCfg.ofMod M (c.sl ACC) (c.sl base) (bitsAt c.n 3) m) size := by
  obtain ⟨n, mo, tmp, minv, red, tight⟩ := M
  simp only at hMn hmo htmp
  subst hMn hmo htmp
  have hn := hc.n0
  have h7 := hc.n10
  have hjm45 : jm < 45 := by rcases hjm with rfl | rfl <;> decide
  have hb45 : base < 45 := by rcases hb with rfl | rfl <;> decide
  have hT : bitsAt c.n 3 + invTbl c.n ≤ size := by
    simp only [bitsAt_eq, invTbl]; show _ ≤ 8192
    have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega)
    omega
  have below : ∀ {i}, i < 45 → c.sl i + 8 * c.n ≤ bitsAt c.n 3 := fun hi => by
    have := sl_below_bits c hi 3 0; omega
  have hbA : base ≠ ACC := by rcases hb with rfl | rfl <;> decide
  have hjA : jm ≠ ACC := by rcases hjm with rfl | rfl <;> decide
  have hjT : jm ≠ TMP := by rcases hjm with rfl | rfl <;> decide
  have hjb : base ≠ jm := by rcases hb with rfl | rfl <;> rcases hjm with rfl | rfl <;> decide
  exact ⟨h4, show c.n < 10 by omega, sl_le c h7 (by decide), sl_le c h7 hb45, hT, sl_le c h7 hjm45,
    sl_le c h7 (by decide), sl_apart c (Ne.symm hbA), Or.inl (below (by decide)), Or.inl (below hb45),
    sl_apart c (by decide), Or.inr (below (i := TMP) (by decide)), sl_apart c hjA, Or.inl (below hjm45),
    sl_apart c hjT⟩

/-- The inversion's writes, within the powers'. -/
theorem invW_pwW {M : Mod} (hMn : M.n = c.n) (htmp : M.tmp = c.sl TMP) {base m : Nat} :
    ∀ w ∈ invW (InvCfg.ofMod M (c.sl ACC) (c.sl base) (bitsAt c.n 3) m),
      ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  obtain ⟨n, mo, tmp, minv, red, tight⟩ := M
  simp only at hMn htmp
  subst hMn htmp
  intro w hw
  simp only [invW, InvCfg.ofMod, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨(c.sl ACC, 8 * c.n), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(bitsAt c.n 3, 64 * c.n + 64), by simp, Nat.le_refl _, by simp only [invTbl]; omega⟩
  · exact ⟨(c.sl TMP, 8 * c.n), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- The power's writes, within the powers'. -/
theorem powW_pwW {P : PowCfg} (h : powW P = slW c [ACC, PT, TMP]) :
    ∀ w ∈ powW P, ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun w hw =>
  ⟨w, List.mem_append_left _ (h ▸ hw), Nat.le_refl _, Nat.le_refl _⟩

/-- `[ACC] = [RZ]^(p-2)` in Montgomery form: by divsteps for up to nine words, else by the power
from the table of the bits of `p - 2`. -/
theorem pPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p)
    (hO : wordsVal s.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) = if (c.C.p - 2).testBit t then 1 else 0) :
    WP isa c.pPow s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Cfg.pPow
  split
  · rename_i h6
    obtain ⟨h4, sp, ip⟩ := hc.inv h6
    exact WP.mono (sp (invLay_of hc h6 h4 (M := c.MP') rfl (jm := MP) rfl (Or.inl rfl) rfl (base := RZ) (Or.inl rfl) c.C.p)
      (by have := hc.p_ge; omega) hpR hs hM hB ip)
      fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwW rfl rfl), lt, v⟩
  · exact WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc) hpR hs hM hB hO hbits
      (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega))
      fun s' ⟨K, U, lt, v⟩ => ⟨K.mono fun r h => List.mem_cons_of_mem _ h, Unch.cover U (powW_pwW (powWP_eq c)), lt, v⟩

/-- `[ACC] = [KM]^(n-2)` in Montgomery form: by divsteps for up to nine words, else by the power
from the table of the bits of `n - 2`. -/
theorem nPow_ok (hc : CfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n)
    (hO : wordsVal s.mem base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0) :
    WP isa c.nPow s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  unfold Cfg.nPow
  split
  · rename_i h
    obtain ⟨hf, h6⟩ := h
    obtain ⟨h4, -, -⟩ := hc.inv h6
    obtain ⟨sn, iN⟩ := hc.inv_n hf h6
    exact WP.mono (sn (invLay_of hc h6 h4 (M := c.MN') rfl (jm := MN) rfl (Or.inr rfl) rfl (base := KM) (Or.inr rfl) c.C.n)
      (by have := hc.n_ge; omega) hnR hs hM hB iN)
      fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwW rfl rfl), lt, v⟩
  · exact WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) hnR hs hM hB hO hbits
      (show c.C.n - 2 < 2 ^ (64 * c.n) by have := hc.n_lt; omega))
      fun s' ⟨K, U, lt, v⟩ => ⟨K.mono fun r h => List.mem_cons_of_mem _ h, Unch.cover U (powW_pwW (powWN_eq c)), lt, v⟩

end VG.Proof.Ecdsa.X86_64
