import VerifiedGarbage.Proof.Ecdsa.X86.InvLays
import VerifiedGarbage.Proof.Weierstrass.X86.ScalarPower

/-! # Field and scalar inversion through the shared divstep backend -/
namespace VG.Proof.Ecdsa.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Mont.X86 VG.Impl.Weierstrass VG.Impl.Weierstrass.X86 VG.Impl.Ecdsa.X86
  VG.Proof.Mont VG.Proof.Mont.X86 VG.Proof.Weierstrass VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass.X86.Inv
variable {c : Cfg}

theorem invW_pwW {M : Mod} (h4 : c.n = 4) (htmp : M.tmp = c.sl TMP) {base m : Nat} :
    ∀ w ∈ invW (InvCfg.ofMod M c.wk (c.sl ACC) (c.sl base) (c.wk + 68) m),
      ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  simp only [invW, InvCfg.ofMod, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · exact ⟨(c.wk, 388), by simp, by omega, by omega⟩
  · exact ⟨(c.sl ACC, 8 * c.n), by simp, Nat.le_refl _, by simp only [h4]; omega⟩
  · exact ⟨(c.sl TMP, 8 * c.n), by simp, by simp only [htmp]; exact Nat.le_refl _, by simp only [htmp, h4]; omega⟩
  · exact ⟨(c.wk, 388), by simp, Nat.le_refl _, by omega⟩

theorem powW_pwW {P : PowCfg} (h7 : c.n < 10)
    (h : powWx P c.wk = slW c [ACC, PT, TMP] ++ [(c.wk, 16 * c.n + 4)]) :
    ∀ w ∈ powWx P c.wk, ∃ w' ∈ pwW c, w'.1 ≤ w.1 ∧ w.1 + w.2 ≤ w'.1 + w'.2 := by
  intro w hw
  rw [h] at hw
  rcases List.mem_append.mp hw with hw | hw
  · exact ⟨w, List.mem_append_left _ hw, Nat.le_refl _, Nat.le_refl _⟩
  · rw [List.mem_singleton.mp hw]
    exact ⟨(c.wk, 388), by simp, Nat.le_refl _, by omega⟩

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
      (base := RZ) (Or.inl rfl) c.C.p) (by have := hc.p_ge; omega)
      (by simpa only [h4] using hR) hs hM (by simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using hB) ok
    refine WP.mono H fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (invW_pwW h4 rfl), ?_, ?_⟩
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using lt
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using v
  · exact WP.mono (powField_ok (P := c.powP) (powLayP hc) (powWkP hc) hR hs hM hB hO hbits he)
      fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (powW_pwW hc.n10 (by rw [powWxP_eq, accLen_MP'])), lt, v⟩

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
      (base := KM) (Or.inr rfl) c.C.n) (by have := hc.n_ge; omega)
      (by simpa only [h4] using hR) hs hM (by simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using hB) ok
    refine WP.mono H fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (invW_pwW h4 rfl), ?_, ?_⟩
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using lt
    · simpa only [h4, wordsVal_eq_val32, InvCfg.ofMod] using v
  · exact WP.mono (powScalar_ok (P := c.powN) (powLayN hc) (powWkN hc) hR hs hM hB hO hbits he)
      fun z ⟨K, U, lt, v⟩ => ⟨K.mono (by decide), Unch.cover U (powW_pwW hc.n10 (by rw [powWxN_eq, accLen_MN'])), lt, v⟩

end VG.Proof.Ecdsa.X86
