module

public import VerifiedGarbage.Proof.Ecdsa.X86_64.Fixed
import VerifiedGarbage.Proof.Ecdsa.X86_64.Stages
import VerifiedGarbage.Proof.Weierstrass.X86_64.SpillUnch
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Mont.X86_64.Wide
import VerifiedGarbage.Proof.Weierstrass.InvMask
import VerifiedGarbage.Proof.X25519.X86_64.Step
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd

/-!
# ECDSA on x86-64: `Z^(p-2)` and `k^(n-2)`

`Cfg.pPowI` and `Cfg.nPowI` are inverses by divsteps for a curve of up to nine
words (`InvSound`; `nPowI` if `fastN`), else powers (`pow_ok`); either leaves `[ACC]` reading as
`[base]^(m - 2)` in Montgomery form, and writes only the slots and the
working area of `pwW` (`pPowI_ok`, `nPowI_ok`). `Cfg.pPow` and `Cfg.nPow`
are calls of the functions `vg_<curve>_inv_mod_p` and `_n` if the curve has
them (`Cfg.inverse`): the divsteps between saving the callee-saved registers
in `PT`'s slot and restoring them (`invFn_ok`), which `pwW` covers; else
`pPowI` and `nPowI` (`pPow_ok`, `nPow_ok`).
-/

@[expose] public section

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Mont VG.Impl.Weierstrass.X86_64 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Mont VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

open VG.Proof.X25519.X86_64 (Keeps Keeps.trans Keeps.mono)

/-- What the powers may write: their slots, and the inversions' working area
past the tables of bits. -/
abbrev pwW (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, PT, TMP] ++ [(bitsAt c.n 3, 64 * c.n + 64)]

theorem rdi_not_invClob (n : Nat) : Reg.rdi ∉ invClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (rdi_not_powClob n)

theorem rsi_not_invClob (n : Nat) : Reg.rsi ∉ invClob n := fun h =>
  (List.mem_cons.mp h).elim (fun h => absurd h (by decide)) (rsi_not_powClob n)

/-- Six words' temporary area, slot `83` (`Cfg.sl`), is past the inversions' working area. -/
theorem tmp6_above (h : c.n = 6) : bitsAt c.n 3 + (64 * c.n + 64) ≤ c.sl TMP := by
  unfold Cfg.sl bitsAt slot; rw [h]; decide

/-- A slot is apart from the inversions' working area. -/
theorem apart_pwA {i : Nat} (hi : i < 45) :
    ∀ w ∈ [(bitsAt c.n 3, 64 * c.n + 64)], c.sl i + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl i := by
  intro w hw
  rw [List.mem_singleton.mp hw]
  by_cases h : i = TMP ∧ c.n = 6
  · obtain ⟨rfl, h6⟩ := h
    exact Or.inr (tmp6_above h6)
  · exact Or.inl (sl_below_bits c hi 3 0 (by
      by_cases hi : i = TMP
      · exact Or.inr ⟨by decide, fun e => h ⟨hi, e⟩⟩
      · exact Or.inl hi))

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
    have := Nat.mul_le_mul_left (64 * c.n + 8) (show j + 1 ≤ 3 by omega_arith)
    rw [Nat.mul_succ] at this; omega_arith
  exact Or.inl (by omega_arith)

/-- The inversions' working area is in the working space. -/
theorem pwA_le (h7 : c.n < 10) : bitsAt c.n 3 + (64 * c.n + 64) ≤ size := by
  simp only [bitsAt_eq]; show _ ≤ 8192
  have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega_arith)
  omega_arith

/-- The flag word apart from what changed. -/
theorem flag_unch_of {base : Addr} {W : List (Nat × Nat)} {m m' : Mem} (hu : Unch base W m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64)
    (hW : ∀ w ∈ W, c.sl FLAG + 8 * c.n ≤ w.1 ∨ w.1 + w.2 ≤ c.sl FLAG) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega_arith)
  rcases hW w hw with h | h
  · exact Or.inl (by omega_arith)
  · exact Or.inr h

/-- The tables of bits are apart from what the powers write. -/
theorem tbl_apart_pwW {j t : Nat} (hj : j < 3) (ht : t < 64 * c.n) (hj1 : j ≠ 1 ∨ c.n ≠ 9 := by sl_or) :
    ∀ w ∈ pwW c, bitsAt c.n j + t + 1 ≤ w.1 ∨ w.1 + w.2 ≤ bitsAt c.n j + t :=
  apart_append (tbl_apart_slW (by decide) j t ht (.inr hj1)) (tbl_apart_pwA hj ht)

/-- The flag word apart from what the powers write. -/
theorem flag_unch_pwW {base : Addr} {m m' : Mem} (hu : Unch base (pwW c) m m')
    (h7 : c.n < 10) (h0 : 0 < c.n) (hn : base.toNat + size ≤ 2 ^ 64) :
    word m' base (c.sl FLAG) = word m base (c.sl FLAG) := by
  have hF := sl_le c h7 (i := FLAG) (by decide)
  refine hu.word (fun w hw => ?_) (by omega_arith)
  rcases apart_pwW (c := c) (i := FLAG) (by decide) (by decide) w hw with h | h
  · exact Or.inl (by omega_arith)
  · exact Or.inr h

/-- The inversions' slots and working area, for up to nine words. -/
theorem invLay_of (hc : BaseCfgOk c) (h6 : c.n ≤ 9) (h4 : 4 ≤ c.n) {M : Mod} (hMn : M.n = c.n) {jm : Nat}
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
    have : 8 * c.n * 45 ≤ 8 * 9 * 45 := Nat.mul_le_mul_right _ (by omega_arith)
    omega_arith
  have below : ∀ {i}, i < 45 → i ≠ TMP → c.sl i + 8 * c.n ≤ bitsAt c.n 3 := fun hi hT => by
    have := sl_below_bits c hi 3 0 (Or.inl hT); omega_arith
  have tbl_tmp : bitsAt c.n 3 + invTbl c.n ≤ c.sl TMP ∨ c.sl TMP + 8 * c.n ≤ bitsAt c.n 3 := by
    by_cases h6 : c.n = 6
    · have := tmp6_above (c := c) h6; exact Or.inl (by unfold invTbl; omega_arith)
    · have := sl_below_bits c (i := TMP) (by decide) 3 0 (Or.inr ⟨by decide, h6⟩); exact Or.inr (by omega_arith)
  have hbA : base ≠ ACC := by rcases hb with rfl | rfl <;> decide
  have hjA : jm ≠ ACC := by rcases hjm with rfl | rfl <;> decide
  have hjT : jm ≠ TMP := by rcases hjm with rfl | rfl <;> decide
  have hjb : base ≠ jm := by rcases hb with rfl | rfl <;> rcases hjm with rfl | rfl <;> decide
  exact ⟨h4, show c.n < 10 by omega_arith, sl_le c h7 (by decide), sl_le c h7 hb45, hT, sl_le c h7 hjm45,
    sl_le c h7 (by decide), sl_apart c (Ne.symm hbA), Or.inl (below (by decide) (by decide)), Or.inl (below hb45 (by rcases hb with rfl | rfl <;> decide)),
    sl_apart c (by decide), tbl_tmp, sl_apart c hjA, Or.inl (below hjm45 hjT),
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
  · exact ⟨(bitsAt c.n 3, 64 * c.n + 64), by simp, Nat.le_refl _, by simp only [invTbl]; omega_arith⟩
  · exact ⟨(c.sl TMP, 8 * c.n), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- The power's writes, within the powers'. -/
theorem powW_pwW {P : PowCfg} (h : powW P = slW c [ACC, PT, TMP]) :
    ∀ w ∈ powW P, ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := fun w hw =>
  ⟨w, List.mem_append_left _ (h ▸ hw), Nat.le_refl _, Nat.le_refl _⟩

/-- `[ACC] = [RZ]^(p-2)` in Montgomery form: by divsteps for up to nine words, else by the power
from the table of the bits of `p - 2`. -/
theorem pPowI_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p)
    (hO : wordsVal s.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p)
    (hbits : ¬ c.n ≤ 9 → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) =
      if (c.C.p - 2).testBit t then 1 else 0) :
    WP isa c.pPowI s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have hpR := unitMod_pow_two hc.p_odd (64 * c.n)
  unfold Cfg.pPowI
  split
  · rename_i h6
    obtain ⟨h4, sp, ip⟩ := hc.inv h6
    exact WP.mono (sp (invLay_of hc h6 h4 (M := c.MPI) rfl (jm := MP) rfl (Or.inl rfl) rfl (base := RZ) (Or.inl rfl) c.C.p)
      (by have := hc.p_ge; omega_arith) hpR hs (hM.adx _) hB ip trivial)
      fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwW rfl rfl), lt, v⟩
  · rename_i h9
    exact WP.mono (pow_ok (P := c.powP) (e := c.C.p - 2) (powLayP hc (by omega_arith)) hpR hs hM hB hO (hbits h9)
      (show c.C.p - 2 < 2 ^ (64 * c.n) by have := hc.p_lt; omega_arith))
      fun s' ⟨K, U, lt, v⟩ => ⟨K.mono fun r h => List.mem_cons_of_mem _ h, Unch.cover U (powW_pwW (powWP_eq c)), lt, v⟩

/-- `[ACC] = [KM]^(n-2)` in Montgomery form: by divsteps for up to nine words, else by the power
from the table of the bits of `n - 2`. -/
theorem nPowI_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n)
    (hO : wordsVal s.mem base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0) :
    WP isa c.nPowI s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have hnR := unitMod_pow_two hc.n_odd (64 * c.n)
  unfold Cfg.nPowI
  split
  · rename_i h
    obtain ⟨hf, h6⟩ := h
    obtain ⟨h4, -, -⟩ := hc.inv h6
    obtain ⟨sn, iN⟩ := hc.inv_n hf h6
    exact WP.mono (sn (invLay_of hc h6 h4 (M := c.MN') rfl (jm := MN) rfl (Or.inr rfl) rfl (base := KM) (Or.inr rfl) c.C.n)
      (by have := hc.n_ge; omega_arith) hnR hs hM hB iN trivial)
      fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwW rfl rfl), lt, v⟩
  · exact WP.mono (pow_ok (P := c.powN) (e := c.C.n - 2) (powLayN hc) hnR hs hM hB hO
      (fun t ht => hbits t (Nat.lt_of_lt_of_le ht (nbitsN_ok hc).2.1)) (nbitsN_ok hc).2.2)
      fun s' ⟨K, U, lt, v⟩ => ⟨K.mono fun r h => List.mem_cons_of_mem _ h, Unch.cover U (powW_pwW (powWN_eq c)), lt, v⟩

/-- The powers call nothing. -/
theorem pPowI_inline (c : Cfg) : c.pPowI.inline = c.pPowI := by
  unfold Cfg.pPowI; split <;> rfl

theorem nPowI_inline (c : Cfg) : c.nPowI.inline = c.nPowI := by
  unfold Cfg.nPowI; split <;> rfl

/-! ## The functions `vg_<curve>_inv_mod_p` and `_n` -/

/-- What the inversions by divsteps write: `pwW` but `PT`'s slot. -/
abbrev pwI (c : Cfg) : List (Nat × Nat) :=
  slW c [ACC, TMP] ++ [(bitsAt c.n 3, 64 * c.n + 64)]

/-- The inversion's writes, within `pwI`. -/
theorem invW_pwI {M : Mod} (hMn : M.n = c.n) (htmp : M.tmp = c.sl TMP) {base m : Nat} :
    ∀ w ∈ invW (InvCfg.ofMod M (c.sl ACC) (c.sl base) (bitsAt c.n 3) m),
      ∃ w' ∈ pwI c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  obtain ⟨n, mo, tmp, minv, red, tight⟩ := M
  simp only at hMn htmp
  subst hMn htmp
  intro w hw
  simp only [invW, InvCfg.ofMod, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact ⟨(c.sl ACC, 8 * c.n), by simp, Nat.le_refl _, Nat.le_refl _⟩
  · exact ⟨(bitsAt c.n 3, 64 * c.n + 64), by simp, Nat.le_refl _, by simp only [invTbl]; omega_arith⟩
  · exact ⟨(c.sl TMP, 8 * c.n), by simp, Nat.le_refl _, Nat.le_refl _⟩

/-- `[ACC] = [RZ]^(p-2)` by divsteps, for up to nine words, writing only `pwI`. -/
theorem invP_ok (hc : BaseCfgOk c) (h9 : c.n ≤ 9) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa (InvCfg.inv c.invP) s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwI c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  obtain ⟨h4, sp, ip⟩ := hc.inv h9
  exact WP.mono (sp (invLay_of hc h9 h4 (M := c.MPI) rfl (jm := MP) rfl (Or.inl rfl) rfl (base := RZ) (Or.inl rfl) c.C.p)
    (by have := hc.p_ge; omega_arith) (unitMod_pow_two hc.p_odd (64 * c.n)) hs (hM.adx _) hB ip trivial)
    fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwI rfl rfl), lt, v⟩

/-- `[ACC] = [KM]^(n-2)` by divsteps, for up to nine words and `fastN`, writing only `pwI`. -/
theorem invN_ok (hc : BaseCfgOk c) (hf : c.fastN = true) (h9 : c.n ≤ 9) {base : Addr} {s : State}
    (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa (InvCfg.inv c.invN) s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwI c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  obtain ⟨h4, -, -⟩ := hc.inv h9
  obtain ⟨sn, iN⟩ := hc.inv_n hf h9
  exact WP.mono (sn (invLay_of hc h9 h4 (M := c.MN') rfl (jm := MN) rfl (Or.inr rfl) rfl (base := KM) (Or.inr rfl) c.C.n)
    (by have := hc.n_ge; omega_arith) (unitMod_pow_two hc.n_odd (64 * c.n)) hs hM hB iN trivial)
    fun s' ⟨K, U, lt, v⟩ => ⟨K, Unch.cover U (invW_pwI rfl rfl), lt, v⟩

theorem invSaved_slots (h6 : 6 ≤ c.n) :
    ∀ p ∈ c.invSaved, c.sl PT ≤ p.2 ∧ p.2 + 8 ≤ c.sl PT + 8 * c.n := by
  intro p hp
  simp only [Cfg.invSaved, Cfg.saved, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith

theorem invSaved_spill (hc : BaseCfgOk c) : Spill.Slots c.invSaved := by
  have := sl_le c hc.n10 (i := PT) (by decide)
  have hsz : size = 8192 := rfl
  refine ⟨fun p hp => ?_, ?_⟩
  · simp only [Cfg.invSaved, Cfg.saved, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only <;> omega_arith
  · simp only [Cfg.invSaved, Cfg.saved, List.map_cons, List.map_nil, List.pairwise_cons,
      List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil,
      false_implies, implies_true, and_true]
    omega_arith

/-- `vg_<curve>_inv_mod_p` or `_n`, for a curve of at least six words (whose
`PT` slot holds the six registers): what its body gives of the memory (`Q`),
from any state whose working space differs from `s`'s only in `PT`'s slot,
the callee-saved registers restored (saved in `PT`'s slot) and the others
outside the body's kept, having written also `PT`'s slot. -/
theorem invFn_ok (hc : BaseCfgOk c) (h6 : 6 ≤ c.n) {body : Prog isa} {base : Addr} {s : State}
    (hs : Scr s base size) {Q : Mem → Prop}
    (hb : ∀ s₁ : State, Scr s₁ base size → Unch base (slW c [PT]) s.mem s₁.mem →
      WP isa body s₁ fun s' => KeepRegs (invClob c.n) s₁ s' ∧ Unch base (pwI c) s₁.mem s'.mem ∧ Q s'.mem) :
    WP isa (c.invFn body) s fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r) ∧
      KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧ Q s'.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hsz : size = 8192 := rfl
  have hpt := sl_le c h7 (i := PT) (by decide)
  have hsl := invSaved_slots (c := c) h6
  rw [show c.invFn body = c.invFnS body from ite_eq_right_of_eq_false _ _ (eq_false (by omega_arith))]
  show WP isa (.seq (.block (Spill.saveCode .rdi c.invSaved)) (.seq body
    (.block (Spill.restoreCode .rdi c.invSaved)))) s _
  -- Save.
  refine WP.seq (WP.mono (Spill.save_ok .rdi c.invSaved s fun p hp => ?_) fun s₁ ⟨g₁, rd₁, wr₁, m₁⟩ => ?_)
  · rw [hs.rdi]
    have := (hsl p hp).2
    exact ⟨_, hs.wr, Offset.contains_base base (by omega_arith) (by omega_arith)⟩
  rw [hs.rdi] at m₁
  have U₁ : Unch base (slW c [PT]) s.mem s₁.mem := m₁ ▸ saveMem_unch _ _ _ _ hsl (by omega_arith)
  have sv₁ : Spill.Saved s₁.mem base s.gpr c.invSaved :=
    m₁ ▸ Spill.saveMem_saved _ _ _ _ (invSaved_spill hc)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hn⟩
  -- The body.
  refine WP.seq (WP.mono (hb s₁ hs₁ U₁) fun s₂ ⟨K₂, U₂, Q₂⟩ => ?_)
  have sv₂ : Spill.Saved s₂.mem base s.gpr c.invSaved := fun p hp => by
    have := hsl p hp
    refine (U₂.word (d := p.2) (fun w hw => ?_) (by omega_arith)).trans (sv₁ p hp)
    rcases apart_append (apart_slW (c := c) (i := PT) (l := [ACC, TMP]) (by decide)) (apart_pwA (by decide))
      w hw with h | h <;> [left; right] <;> omega_arith
  have rdi₂ : s₂.gpr .rdi = base := by rw [K₂.gpr _ (rdi_not_invClob _), g₁, hs.rdi]
  -- Restore.
  refine WP.mono (Spill.restore_ok .rdi c.invSaved s.gpr s₂ (by
      simp [Cfg.invSaved, Cfg.saved]) (fun p hp => ?_) (by rw [rdi₂]; exact sv₂))
    fun s' ⟨gs, go, ms, rds, wrs⟩ => ?_
  · rw [rdi₂, K₂.wr, wr₁]
    have := (hsl p hp).2
    exact ⟨_, List.mem_append_right _ hs.wr, Offset.contains_base base (by omega_arith) (by omega_arith)⟩
  have hsv : c.invSaved.map Prod.fst = Cfg.saved.map Prod.fst := by
    simp [Cfg.invSaved, Cfg.saved]
  rw [hsv] at gs go
  refine ⟨gs, ⟨fun r hr => ?_, by rw [rds, K₂.rd, rd₁], by rw [wrs, K₂.wr, wr₁]⟩, ?_, by rw [ms]; exact Q₂⟩
  · by_cases h : r ∈ Cfg.saved.map Prod.fst
    · exact gs r h
    · rw [go r h, K₂.gpr r hr, g₁]
  · refine Unch.mono (ms ▸ U₁.trans U₂ : Unch base (slW c [PT] ++ pwI c) s.mem s'.mem) fun w hw => ?_
    simp only [pwI, pwW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with rfl | rfl | rfl | rfl <;> simp

private theorem setXmm_gpr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).gpr = s.gpr := rfl
private theorem setXmm_mem (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).mem = s.mem := rfl
private theorem setXmm_rd (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).rd = s.rd := rfl
private theorem setXmm_wr (s : State) (r : XReg) (v : BitVec 128) : (s.setXmm r v).wr = s.wr := rfl

/-- Copying the callee-saved registers into `xmm` registers changes nothing
else that the proofs follow. -/
theorem savesX_ok (s : State) :
    WP isa (.block (Cfg.invKeptX.map fun (r, x) => Instr.xop (.movq x r))) s fun t =>
      t.gpr = s.gpr ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Cfg.invKeptX, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    XOp.exec, Option.some.injEq, exists_eq_left', setXmm_gpr, setXmm_mem, setXmm_rd, setXmm_wr, and_self]

/-- Copying them back writes only them. -/
theorem restoresX_ok (s : State) :
    WP isa (.block (Cfg.invKeptX.map fun (r, x) => Instr.movqR r x)) s fun t =>
      (∀ r, r ∉ Cfg.invKeptX.map Prod.fst → t.gpr r = s.gpr r) ∧ t.mem = s.mem ∧ t.rd = s.rd ∧
        t.wr = s.wr := by
  apply WP.of_runBlock
  simp only [Cfg.invKeptX, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil, exec,
    Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg_of_ne _ _ hr.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.1,
    RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.1, RegUpd.gpr_setReg_of_ne _ _ hr.2.2.2.2.2]

/-- The inversion of four or five words may write every callee-saved
register. -/
theorem invKeptX_clob {n : Nat} (h : n = 4 ∨ n = 5) : ∀ r ∈ Cfg.invKeptX.map Prod.fst, r ∈ invClob n := by
  rcases h with rfl | rfl <;> decide

/-- `vg_<curve>_inv_mod_p` or `_n` for fewer than six words (four or five): its body
from a state of the same memory and registers, the callee-saved registers
copied to `xmm` registers and back, which `invClob` allows. -/
theorem invFnX_ok (hc : BaseCfgOk c) (h6 : c.n < 6) {body : Prog isa} {base : Addr} {s : State}
    (hs : Scr s base size) {Q : Mem → Prop}
    (hb : ∀ s₁ : State, Scr s₁ base size → s₁.mem = s.mem → (∀ r, s₁.gpr r = s.gpr r) →
      WP isa body s₁ fun s' => KeepRegs (invClob c.n) s₁ s' ∧ Unch base (pwI c) s₁.mem s'.mem ∧ Q s'.mem) :
    WP isa (c.invFn body) s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      Q s'.mem := by
  have h4 : c.n = 4 ∨ c.n = 5 := by have := (hc.inv (by omega_arith)).1; omega_arith
  rw [show c.invFn body = Cfg.invFnX body from ite_eq_left_of_eq_true _ _ (eq_true h6)]
  refine WP.seq (WP.mono (savesX_ok s) fun s₁ ⟨g₁, m₁, rd₁, wr₁⟩ => ?_)
  have hs₁ : Scr s₁ base size := ⟨by rw [g₁]; exact hs.rdi, by rw [wr₁]; exact hs.wr, hs.nowrap⟩
  refine WP.seq (WP.mono (hb s₁ hs₁ m₁ (fun r => by rw [g₁])) fun s₂ ⟨K₂, U₂, Q₂⟩ => ?_)
  refine WP.mono (restoresX_ok s₂) fun s' ⟨g', m', rd', wr'⟩ => ⟨⟨fun r hr => ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [g' r (fun h => hr (invKeptX_clob h4 r h)), K₂.gpr r hr, g₁]
  · rw [rd', K₂.rd, rd₁]
  · rw [wr', K₂.wr, wr₁]
  · rw [m', ← m₁]
    refine U₂.mono fun w hw => ?_
    simp only [pwI, pwW, slW, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    rcases hw with rfl | rfl | rfl <;> simp
  · rw [m']; exact Q₂

/-- `vg_<curve>_inv_mod_p`'s body run as a function, for six to nine words:
`[ACC] = [RZ]^(p-2)`, the callee-saved registers restored. -/
theorem invPFn_ok (hc : BaseCfgOk c) (h6 : 6 ≤ c.n) (h9 : c.n ≤ 9) {base : Addr} {s : State}
    (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa (c.invFn c.pPowI) s fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r) ∧
      KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  rw [show c.pPowI = InvCfg.inv c.invP from ite_eq_left_of_eq_true _ _ (eq_true h9)]
  refine invFn_ok hc h6 hs (Q := fun m => wordsVal m base (c.sl ACC) c.n < c.C.p ∧
    toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (c.sl ACC) c.n) =
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2)) fun s₁ hs₁ U₁ => ?_
  have hrz : wordsVal s₁.mem base (c.sl RZ) c.n = wordsVal s.mem base (c.sl RZ) c.n :=
    sv_unch U₁ h7 hn (i := RZ) (by decide) (apart_slW (by decide))
  refine WP.mono (invP_ok hc h9 hs₁ (hM.unch U₁ (apart_slW (i := MP) (by decide)) hn) (hrz ▸ hB))
    fun s' ⟨K, U, lt, v⟩ => ⟨K, U, lt, by rw [v, hrz]⟩

/-- `vg_<curve>_inv_mod_n`'s body run as a function, for six to nine words
and `fastN`: `[ACC] = [KM]^(n-2)`, the callee-saved registers restored. -/
theorem invNFn_ok (hc : BaseCfgOk c) (h6 : 6 ≤ c.n) (h9 : c.n ≤ 9) (hf : c.fastN = true) {base : Addr}
    {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa (c.invFn c.nPowI) s fun s' => (∀ r ∈ Cfg.saved.map Prod.fst, s'.gpr r = s.gpr r) ∧
      KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  rw [show c.nPowI = InvCfg.inv c.invN from ite_eq_left_of_eq_true _ _ (eq_true ⟨hf, h9⟩)]
  refine invFn_ok hc h6 hs (Q := fun m => wordsVal m base (c.sl ACC) c.n < c.C.n ∧
    toM c.C.n (2 ^ (64 * c.n)) (wordsVal m base (c.sl ACC) c.n) =
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2)) fun s₁ hs₁ U₁ => ?_
  have hkm : wordsVal s₁.mem base (c.sl KM) c.n = wordsVal s.mem base (c.sl KM) c.n :=
    sv_unch U₁ h7 hn (i := KM) (by decide) (apart_slW (by decide))
  refine WP.mono (invN_ok hc hf h9 hs₁ (hM.unch U₁ (apart_slW (i := MN) (by decide)) hn) (hkm ▸ hB))
    fun s' ⟨K, U, lt, v⟩ => ⟨K, U, lt, by rw [v, hkm]⟩

/-- `vg_<curve>_inv_mod_p`'s body run as a function, for fewer than six words:
`[ACC] = [RZ]^(p-2)`. -/
theorem invPFnX_ok (hc : BaseCfgOk c) (h6 : c.n < 6) (h9 : c.n ≤ 9) {base : Addr} {s : State}
    (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p) :
    WP isa (c.invFn c.pPowI) s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  rw [show c.pPowI = InvCfg.inv c.invP from ite_eq_left_of_eq_true _ _ (eq_true h9)]
  refine invFnX_ok hc h6 hs (Q := fun m => wordsVal m base (c.sl ACC) c.n < c.C.p ∧
    toM c.C.p (2 ^ (64 * c.n)) (wordsVal m base (c.sl ACC) c.n) =
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2)) fun s₁ hs₁ m₁ _ => ?_
  rw [← m₁] at hM hB
  refine WP.mono (invP_ok hc h9 hs₁ hM hB) fun s' ⟨K, U, lt, v⟩ => ⟨K, U, lt, by rw [v, m₁]⟩

/-- `vg_<curve>_inv_mod_n`'s body run as a function, for fewer than six words
and `fastN`: `[ACC] = [KM]^(n-2)`. -/
theorem invNFnX_ok (hc : BaseCfgOk c) (h6 : c.n < 6) (h9 : c.n ≤ 9) (hf : c.fastN = true) {base : Addr}
    {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n) :
    WP isa (c.invFn c.nPowI) s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  rw [show c.nPowI = InvCfg.inv c.invN from ite_eq_left_of_eq_true _ _ (eq_true ⟨hf, h9⟩)]
  refine invFnX_ok hc h6 hs (Q := fun m => wordsVal m base (c.sl ACC) c.n < c.C.n ∧
    toM c.C.n (2 ^ (64 * c.n)) (wordsVal m base (c.sl ACC) c.n) =
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2)) fun s₁ hs₁ m₁ _ => ?_
  rw [← m₁] at hM hB
  refine WP.mono (invN_ok hc hf h9 hs₁ hM hB) fun s' ⟨K, U, lt, v⟩ => ⟨K, U, lt, by rw [v, m₁]⟩

/-! ## The inversions that four-word curves share -/

/-- `[d] = k`, through `rax`. -/
theorem immStore_ok {base : Addr} {s : State} (hs : Scr s base size) (k : BitVec 64) {d : Nat}
    (hd : d + 8 ≤ size) :
    WP isa (.block [.movImm64 .rax k, .store (sc d) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base d) k ∧ KeepRegs [.rax] s t := by
  rw [← List.singleton_append, WP.block_append_iff]
  obtain h : WP isa (.block [.movImm64 .rax k]) s fun v => v.gpr .rax = k ∧ Keeps [.rax] s v := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg_self, Option.some.injEq,
      exists_eq_left']
    refine ⟨trivial, fun r hr => ?_, rfl, rfl, rfl⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [RegUpd.gpr_setReg_of_ne _ _ hr]
  refine WP.mono h fun s₁ ⟨g₁, k₁⟩ => ?_
  refine WP.mono (storeReg_ok (hs.of_keeps k₁ (by decide)) .rax hd) fun t ⟨mt, _, _, kt⟩ =>
    ⟨by rw [mt, g₁, k₁.2.1], (Keeps.regs k₁).trans (kt.mono (by decide))⟩

/-- Words `0 … j - 1` of `seed` at `d`. -/
theorem constRows_ok {base : Addr} {s : State} (hs : Scr s base size) (seed : Nat) {d : Nat} :
    ∀ j, d + 8 * j ≤ size → WP isa (.block ((List.range j).flatMap fun i =>
      [.movImm64 .rax (BitVec.ofNat 64 (seed >>> (64 * i))), .store (sc (d + 8 * i)) .rax])) s fun t =>
        wordsVal t.mem base d j = seed % 2 ^ (64 * j) ∧ KeepRegs [.rax] s t ∧ Outside base d (8 * j) s.mem t.mem
  | 0, _ => WP.block_nil ⟨by simp only [wordsVal, Nat.mul_zero, Nat.pow_zero, Nat.mod_one],
      ⟨fun _ _ => rfl, rfl, rfl⟩, Outside.refl _ _ _ _⟩
  | j + 1, hj => by
    have hn := hs.nowrap
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, WP.block_append_iff]
    refine WP.mono (constRows_ok hs seed j (by omega_using [hj])) fun s₁ ⟨e₁, k₁, O₁⟩ => ?_
    refine WP.mono (immStore_ok (hs.of_keepRegs k₁ (by decide)) _ (d := d + 8 * j) (by omega_using [hj]))
      fun t ⟨mt, kt⟩ => ?_
    obtain Ot := writeW_outside s₁.mem base (d := d + 8 * j) (BitVec.ofNat 64 (seed >>> (64 * j)))
      (by omega_using [hj, hn])
    refine ⟨?_, k₁.trans kt, fun x hx => by rw [mt, Ot x (by omega_using [hx]), O₁ x (by omega_using [hx])]⟩
    rw [wordsVal_succ_top, mt, word_writeW_self, Ot.wordsVal (by omega_using []) (by omega_using [hj, hn]), e₁,
      pow64_succ, Nat.mul_comm (2 ^ 64), Nat.mod_mul, const_word]

/-- The stores of a shared inversion's constants: `-m⁻¹ mod 2^64` in `TMP`'s
slot and the seed in `PT`'s. -/
theorem invConsts_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size) (M : Mod)
    (seed : Nat) :
    WP isa (.block (c.invConsts M seed)) s fun t => word t.mem base (c.sl TMP) = M.minv ∧
      wordsVal t.mem base (c.sl PT) c.n = seed % 2 ^ (64 * c.n) ∧ KeepRegs [.rax] s t ∧
      Unch base (slW c [PT, TMP]) s.mem t.mem := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hpt := sl_le c h7 (i := PT) (by decide)
  have htm := sl_le c h7 (i := TMP) (by decide)
  have h0 := hc.n0
  obtain hap := sl_apart c (i := PT) (j := TMP) (by decide)
  rw [Cfg.invConsts, WP.block_append_iff]
  refine WP.mono (immStore_ok hs M.minv (d := c.sl TMP) (by omega_using [htm, h0])) fun s₁ ⟨m₁, k₁⟩ => ?_
  obtain O₁ := writeW_outside s.mem base (d := c.sl TMP) M.minv (by omega_using [htm, hn, h0])
  refine WP.mono (constRows_ok (hs.of_keepRegs k₁ (by decide)) seed c.n hpt) fun t ⟨e, kt, Ot⟩ =>
    ⟨?_, e, k₁.trans kt, fun x hx => ?_⟩
  · rw [Ot.word (by omega_using [hap, h0]) (by omega_using [htm, hn, h0]), m₁, word_writeW_self]
  · simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hx
    rw [Ot x (by omega_using [hx]), m₁, O₁ x (by omega_using [hx, h0])]

/-- A shared inversion's body from the stores of its constants: `[ACC] =
[base]^(m - 2)`, for `P` the configuration modulo `m` with the seed in
`PT`'s slot and `-m⁻¹ mod 2^64` in `TMP`'s. -/
theorem invS_ok (hc : BaseCfgOk c) (h6 : c.n < 6) (h9 : c.n ≤ 9) (h4 : 4 ≤ c.n) {M : Mod} {m : Nat} [NeZero m]
    (hMn : M.n = c.n) {jm : Nat} (hmo : M.mo = c.sl jm) (hjm : jm = MP ∨ jm = MN) (htmp : M.tmp = c.sl TMP)
    {bs : Nat} (hb : bs = RZ ∨ bs = KM) (hS : InvSound m) (hOk : InvOk (InvCfg.ofMod M (c.sl ACC) (c.sl bs)
      (bitsAt c.n 3) m) m) (hm2 : 2 < m) (hR : UnitMod m (2 ^ (64 * c.n)))
    {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW M size m s.mem base) (hB : wordsVal s.mem base (c.sl bs) c.n < m) :
    WP isa (.seq (.block (c.invConsts M ((InvCfg.ofModS M (c.sl ACC) (c.sl bs) (bitsAt c.n 3) m (c.sl PT)
        (c.sl TMP)).seedOf m)))
      (c.invFn (InvCfg.inv (InvCfg.ofModS M (c.sl ACC) (c.sl bs) (bitsAt c.n 3) m (c.sl PT) (c.sl TMP))))) s
      fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
        wordsVal s'.mem base (c.sl ACC) c.n < m ∧
        toM m (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
          toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl bs) c.n) ^ (m - 2) := by
  have h7 := hc.n10
  have hn := hs.nowrap
  have hb45 : bs < 45 := by rcases hb with rfl | rfl <;> decide
  have hjm45 : jm < 45 := by rcases hjm with rfl | rfl <;> decide
  obtain hbP : bs ∉ [PT, TMP] := by rcases hb with rfl | rfl <;> decide
  obtain hjP : jm ∉ [PT, TMP] := by rcases hjm with rfl | rfl <;> decide
  refine WP.seq (WP.mono (invConsts_ok hc hs M _) fun s₁ ⟨w₁, v₁, K₁, U₁⟩ => ?_)
  obtain hs₁ := hs.of_keepRegs K₁ (by decide)
  obtain hrz : wordsVal s₁.mem base (c.sl bs) c.n = wordsVal s.mem base (c.sl bs) c.n :=
    sv_unch U₁ h7 hn hb45 (apart_slW hbP)
  obtain hM₁ : ModOkW M size m s₁.mem base := hM.unch U₁ (by rw [hmo, hMn]; exact apart_slW hjP) hn
  refine WP.mono (invFnX_ok hc h6 hs₁ (Q := fun mm => wordsVal mm base (c.sl ACC) c.n < m ∧
    toM m (2 ^ (64 * c.n)) (wordsVal mm base (c.sl ACC) c.n) =
      toM m (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl bs) c.n) ^ (m - 2)) fun s₂ hs₂ m₂ _ => ?_)
    fun s' ⟨K, U, Q⟩ => ⟨(K₁.mono fun r h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h; subst h; simp [invClob, powClob, clob]).trans K, (U₁.trans U).mono fun w hw => by
      rcases List.mem_append.mp hw with h | h
      · refine List.mem_append_left _ ?_
        simp only [slW, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rcases h with h | h <;> simp [h]
      · exact h, Q⟩
  rw [← m₂] at hM₁ hrz w₁ v₁
  obtain hL := (invLay_of hc h9 h4 hMn hmo hjm htmp hb m).withSeed (some (c.sl PT, c.sl TMP))
  obtain hmP : m < 2 ^ (64 * c.n) := hMn ▸ (hM.val ▸ wordsVal_lt _ _ _ _)
  obtain hSd : SeedOk (InvCfg.ofModS M (c.sl ACC) (c.sl bs) (bitsAt c.n 3) m (c.sl PT) (c.sl TMP))
      size m s₂.mem base := by
    obtain hse : (InvCfg.ofModS M (c.sl ACC) (c.sl bs) (bitsAt c.n 3) m (c.sl PT) (c.sl TMP)).seed =
      some (c.sl PT, c.sl TMP) := rfl
    simp only [SeedOk, hse]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show c.sl PT + 8 * M.n ≤ size
      rw [hMn]; exact sl_le c h7 (by decide)
    · show c.sl TMP + 8 ≤ size
      have := sl_le c h7 (i := TMP) (by decide); omega_using [this, hc.n0]
    · show c.sl PT + 8 * M.n ≤ bitsAt c.n 3 ∨ _
      rw [hMn]; exact Or.inl (sl_below_bits c (i := PT) (by decide) 3 0)
    · show wordsVal s₂.mem base (c.sl PT) M.n = _
      rw [hMn, v₁, Nat.mod_eq_of_lt]
      exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega_using [hm2])) hmP.le
    · exact w₁
  refine WP.mono (hS hL hm2 (show UnitMod m (2 ^ (64 * M.n)) by rw [hMn]; exact hR) hs₂ hM₁
    (show wordsVal s₂.mem base (c.sl bs) M.n < m by rw [hMn, hrz]; exact hB)
    (hOk.withSeed (some (c.sl PT, c.sl TMP))) hSd)
    fun s' ⟨K, U, lt, v⟩ => by
      have K' : KeepRegs (invClob M.n) s₂ s' := K
      have lt' : wordsVal s'.mem base (c.sl ACC) M.n < m := lt
      have v' : toM m (2 ^ (64 * M.n)) (wordsVal s'.mem base (c.sl ACC) M.n) =
          toM m (2 ^ (64 * M.n)) (wordsVal s₂.mem base (c.sl bs) M.n) ^ (m - 2) := v
      rw [hMn] at K' lt' v'
      exact ⟨K', Unch.cover U (invW_pwI hMn htmp (base := bs) (m := m)), lt', by rw [v', hrz]⟩

/-- `[ACC] = [RZ]^(p-2)` in Montgomery form: a call of
`vg_<curve>_inv_mod_p` (`invPFn_ok`, `invPFnX_ok`), or inline (`pPowI_ok`). -/
theorem pPow_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MP' size c.C.p s.mem base) (hB : wordsVal s.mem base (c.sl RZ) c.n < c.C.p)
    (hO : wordsVal s.mem base (c.sl ONEP) c.n = 2 ^ (64 * c.n) % c.C.p)
    (hbits : ¬ c.n ≤ 9 → ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 1 + t)) =
      if (c.C.p - 2).testBit t then 1 else 0) :
    WP isa c.pPow.inline s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.p ∧
      toM c.C.p (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.p (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl RZ) c.n) ^ (c.C.p - 2) := by
  unfold Cfg.pPow
  cases hi : c.inverse with
  | none => rw [pPowI_inline]; exact pPowI_ok hc hs hM hB hO hbits
  | some C =>
    obtain ⟨h9, -⟩ := hc.inverse (by rw [hi]; rfl)
    dsimp only
    by_cases hv : c.inv4 = true
    · obtain ⟨h4, sp, ip⟩ := hc.inv h9
      rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
      exact invS_ok hc (by have := hc.inv4_n hv; omega_arith) h9 h4 (M := c.MP') rfl (jm := MP) rfl (Or.inl rfl) rfl
        (bs := RZ) (Or.inl rfl) sp ⟨ip.B1, ip.B16, ip.C, ip.Cpos, ip.Cn, ip.bound⟩ (by have := hc.p_ge; omega_arith) (unitMod_pow_two hc.p_odd (64 * c.n)) hs hM hB
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    by_cases h6 : 6 ≤ c.n
    · exact WP.mono (invPFn_ok hc h6 h9 hs hM hB) fun _ h => h.2
    · exact invPFnX_ok hc (by omega_arith) h9 hs hM hB

/-- `[ACC] = [KM]^(n-2)` in Montgomery form: a call of
`vg_<curve>_inv_mod_n` (`invNFn_ok`, `invNFnX_ok`), or inline (`nPowI_ok`). -/
theorem nPow_ok (hc : BaseCfgOk c) {base : Addr} {s : State} (hs : Scr s base size)
    (hM : ModOkW c.MN' size c.C.n s.mem base) (hB : wordsVal s.mem base (c.sl KM) c.n < c.C.n)
    (hO : wordsVal s.mem base (c.sl ONEN) c.n = 2 ^ (64 * c.n) % c.C.n)
    (hbits : ∀ t < 64 * c.n, s.mem (off base (bitsAt c.n 2 + t)) = if (c.C.n - 2).testBit t then 1 else 0) :
    WP isa c.nPow.inline s fun s' => KeepRegs (invClob c.n) s s' ∧ Unch base (pwW c) s.mem s'.mem ∧
      wordsVal s'.mem base (c.sl ACC) c.n < c.C.n ∧
      toM c.C.n (2 ^ (64 * c.n)) (wordsVal s'.mem base (c.sl ACC) c.n) =
        toM c.C.n (2 ^ (64 * c.n)) (wordsVal s.mem base (c.sl KM) c.n) ^ (c.C.n - 2) := by
  unfold Cfg.nPow
  cases hi : c.inverse with
  | none => rw [nPowI_inline]; exact nPowI_ok hc hs hM hB hO hbits
  | some C =>
    obtain ⟨h9, hf⟩ := hc.inverse (by rw [hi]; rfl)
    dsimp only
    by_cases hv : c.inv4 = true
    · obtain ⟨h4, -, -⟩ := hc.inv h9
      obtain ⟨sn, iN⟩ := hc.inv_n hf h9
      rw [ite_eq_left_of_eq_true _ _ (eq_true hv)]
      exact invS_ok hc (by have := hc.inv4_n hv; omega_arith) h9 h4 (M := c.MN') rfl (jm := MN) rfl (Or.inr rfl) rfl
        (bs := KM) (Or.inr rfl) sn iN (by have := hc.n_ge; omega_arith) (unitMod_pow_two hc.n_odd (64 * c.n)) hs hM hB
    rw [ite_eq_right_of_eq_false _ _ (eq_false hv)]
    by_cases h6 : 6 ≤ c.n
    · exact WP.mono (invNFn_ok hc h6 h9 hf hs hM hB) fun _ h => h.2
    · exact invNFnX_ok hc (by omega_arith) h9 hf hs hM hB

end VG.Proof.Ecdsa.X86_64
