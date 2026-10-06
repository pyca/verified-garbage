import VerifiedGarbage.Proof.Ecdsa.X86.Setup

/-!
# ECDSA on x86 (32-bit): field operations on numbered slots

The Montgomery operations of `Proof/Mont/X86/Ops.lean` on the slots
`c.sl i` of the working space, modulo `p` (`c.MP'`) or `n` (`c.MN'`), with the
accumulator at `c.wk`: an operation writing slot `o` keeps every other slot
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
    (h : OpKeep M base c.wk (c.sl o) s s') {i : Nat} (hi : i < 45) (hio : i ≠ o) (hit : i ≠ TMP) :
    sv c base s' i = sv c base s i := by
  have hl := sl_le c h7 hi
  have hk := sl_below_wk c hi
  refine h.unch.wordsVal (fun w hw => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · rw [hMn]; exact sl_apart c hio
  · rw [hMn, hMt]; exact sl_apart c hit
  · exact .inl hk

/-- The modulus in slot `j` survives an operation writing another slot. -/
theorem _root_.VG.Proof.Mont.ModOkW.keepX86 {M M' : Mod} {m : Nat} {base : Addr} {s s' : State}
    (hM : ModOkW M size m s.mem base) {j : Nat} (hj : j < 45) (hmo : M.mo = c.sl j) (hMn : M.n = c.n)
    (hM'n : M'.n = c.n) (hM't : M'.tmp = c.sl TMP) (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32)
    {o : Nat} (h : OpKeep M' base c.wk (c.sl o) s s') (hjo : j ≠ o) (hjt : j ≠ TMP) :
    ModOkW M size m s'.mem base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by
    have := sv_keep hM'n hM't h7 hn h hj hjo hjt
    simp only [sv] at this
    rw [hmo, hMn, this, ← hMn, ← hmo]; exact hM.val, hM.inv, hM.red⟩

/-- The operations' layout on numbered slots. -/
theorem slLay {M : Mod} (hMn : M.n = c.n) (hmo : M.mo = c.sl MP ∨ M.mo = c.sl MN) (hMt : M.tmp = c.sl TMP)
    (h7 : c.n < 10) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45) (hot : o ≠ TMP) :
    OpLay M size c.wk (c.sl o) (c.sl a) (c.sl b) := by
  have hk := wk_le c h7 hMn
  have := sl_below_wk c ho; have := sl_below_wk c ha; have := sl_below_wk c hb
  have := sl_below_wk c (i := TMP) (by decide)
  have hm : M.mo + 8 * M.n ≤ c.wk := by
    rcases hmo with h | h <;> rw [h, hMn]
    · exact sl_below_wk c (by decide)
    · exact sl_below_wk c (by decide)
  rw [hMn] at hm
  obtain ⟨n, mo, tmp, minv⟩ := M
  simp only at hMn hMt hm
  subst hMn hMt
  exact ⟨hk, sl_le c h7 ho, sl_le c h7 ha, sl_le c h7 hb, .inr (sl_below_wk c ho),
    .inr (sl_below_wk c ha), .inr (sl_below_wk c hb), .inr hm, .inr (sl_below_wk c (by decide)),
    sl_apart c hot⟩

/-- `[o] = [a] [b] R⁻¹ mod m`, on slots. -/
theorem slMul_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (hmo : M.mo = c.sl MP ∨ M.mo = c.sl MN)
    (hMt : M.tmp = c.sl TMP) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hot : o ≠ TMP) (hB : sv c base s b < m) :
    WP isa (mul M c.wk (c.sl o) (c.sl a) (c.sl b)) s fun s' => OpKeep M base c.wk (c.sl o) s s' ∧
      sv c base s' o < m ∧ sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  have := mul_ok hs hM (slLay hMn hmo hMt h7 ho ha hb hot) (by rw [hMn]; exact hB)
  rw [hMn] at this
  exact this

/-- `[o] = ([a] + [b]) mod m`, on slots. -/
theorem slAdd_ok {M : Mod} {m : Nat} (hMn : M.n = c.n) (hmo : M.mo = c.sl MP ∨ M.mo = c.sl MN)
    (hMt : M.tmp = c.sl TMP) (h7 : c.n < 10) {base : Addr} {s : State}
    (hs : Scr s base size) (hM : ModOkW M size m s.mem base) {o a b : Nat} (ho : o < 45)
    (ha : a < 45) (hb : b < 45) (hot : o ≠ TMP) (hAB : sv c base s a + sv c base s b < 2 * m) :
    WP isa (.block (add M c.wk (c.sl o) (c.sl a) (c.sl b))) s fun s' => OpKeep M base c.wk (c.sl o) s s' ∧
      sv c base s' o = (sv c base s a + sv c base s b) % m := by
  have := add_ok hs hM (slLay hMn hmo hMt h7 ho ha hb hot) (by rw [hMn]; exact hAB)
  rw [hMn] at this
  exact this

end VG.Proof.Ecdsa.X86
