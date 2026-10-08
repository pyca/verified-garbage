import VerifiedGarbage.Proof.Ecdsa.X86.Setup

/-!
# ECDSA on x86 (32-bit): field operations on numbered slots

The calls of the Montgomery functions (`CallOps.lean`) on the slots `c.sl i`
of the working space, modulo `p` (`c.SP`) or `n` (`c.SN`), with their own
working space at `c.wk`: an operation writing slot `o` keeps every other slot
but the temporary area's (`sv_keep`) and the moduli (`ModOkW.keepX86`).
-/

namespace VG.Proof.Ecdsa.X86

open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
open VG.Impl.Ecdsa.X86
open VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass.X86 VG.Proof.Weierstrass Spec.Weierstrass

variable {c : Cfg}

theorem MP'_n (c : Cfg) : c.MP'.n = c.n := rfl
theorem MN'_n (c : Cfg) : c.MN'.n = c.n := rfl
theorem MP'_tmp (c : Cfg) : c.MP'.tmp = c.sl TMP := rfl
theorem MN'_tmp (c : Cfg) : c.MN'.tmp = c.sl TMP := rfl
theorem MP'_mo (c : Cfg) : c.MP'.mo = c.sl MP := rfl
theorem MN'_mo (c : Cfg) : c.MN'.mo = c.sl MN := rfl

/-- A slot apart from what an operation writes keeps its number. -/
theorem sv_keep {M : Mod} (hMn : M.n = c.n) (hMt : M.tmp = c.sl TMP) (h7 : c.n < 10)
    {base : Addr} (hn : base.toNat + size ≤ 2 ^ 32) {o : Nat} {s s' : State}
    (h : CKeep M base c.wk (c.sl o) s s') {i : Nat} (hi : i < 45) (hio : i ≠ o) (hit : i ≠ TMP) :
    sv c base s' i = sv c base s i := by
  have hl := sl_le c h7 hi
  have hk := sl_below_wk c hi
  have := wk_own c
  refine h.unch.wordsVal (fun w hw => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · rw [hMn]; exact sl_apart c hio
  · rw [hMn, hMt]; exact sl_apart c hit
  · exact .inl hk
  · exact .inl (by simp only; omega)

/-- The modulus in slot `j` survives an operation writing another slot. -/
theorem _root_.VG.Proof.Mont.ModOkW.keepX86 {M M' : Mod} {m : Nat} {base : Addr} {s s' : State}
    (hM : ModOkW M size m s.mem base) {j : Nat} (hj : j < 45) (hmo : M.mo = c.sl j) (hMn : M.n = c.n)
    (hM'n : M'.n = c.n) (hM't : M'.tmp = c.sl TMP) (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32)
    {o : Nat} (h : CKeep M' base c.wk (c.sl o) s s') (hjo : j ≠ o) (hjt : j ≠ TMP) :
    ModOkW M size m s'.mem base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by
    have := sv_keep hM'n hM't h7 hn h hj hjo hjt
    simp only [sv] at this
    rw [hmo, hMn, this, ← hMn, ← hmo]; exact hM.val, hM.inv, hM.red⟩

/-- The calls' facts on numbered slots. -/
theorem slCall {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {m : Nat} (hMn : M.n = c.n)
    (hF : F.k = c.n ∧ F.m = m ∧ Mont.FnOk F) : CallCfg F M m size c.wk :=
  ⟨hF.2.2, hF.1.trans hMn.symm, hF.2.1, rfl, by rw [hMn]⟩

/-- `[o] = [a] [b] R⁻¹ mod m`, on slots. -/
theorem slMul_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {m : Nat} (hMn : M.n = c.n)
    (hF : F.k = c.n ∧ F.m = m ∧ Mont.FnOk F) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hB : sv c base s b < m) :
    WP isa (Mont.mulCall F (c.sl o) (c.sl a) (c.sl b)) s fun s' => CKeep M base c.wk (c.sl o) s s' ∧
      sv c base s' o < m ∧ sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  have := mulC_ok (slCall hMn hF) hs (by rw [hMn]; exact sl_below_wk c ho) (by rw [hMn]; exact sl_below_wk c ha)
    (by rw [hMn]; exact sl_below_wk c hb) (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

/-- `[o] = ([a] + [b]) mod m`, on slots. -/
theorem slAdd_ok {F : Spec.Weierstrass.Mont.Modulus} {M : Mod} {m : Nat} (hMn : M.n = c.n)
    (hF : F.k = c.n ∧ F.m = m ∧ Mont.FnOk F) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hAB : sv c base s a + sv c base s b < 2 * m) :
    WP isa (Mont.addCall F (c.sl o) (c.sl a) (c.sl b)) s fun s' => CKeep M base c.wk (c.sl o) s s' ∧
      sv c base s' o = (sv c base s a + sv c base s b) % m := by
  have := addC_ok (slCall hMn hF) hs (by rw [hMn]; exact sl_below_wk c ho) (by rw [hMn]; exact sl_below_wk c ha)
    (by rw [hMn]; exact sl_below_wk c hb) (by rw [hMn]; exact hAB)
  rw [hMn] at this
  exact this

end VG.Proof.Ecdsa.X86
