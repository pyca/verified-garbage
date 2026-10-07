import VerifiedGarbage.Proof.Ecdsa.Arm.Setup

/-!
# ECDSA on 32-bit ARM: field operations on numbered slots

The calls of the Montgomery arithmetic's functions
(`Proof/Weierstrass/Arm/MontCall.lean`) on the slots `c.sl i` of the working
space, modulo `p` (`c.SP`) or `n` (`c.SN`), whose own working space is at
`c.wk`: an operation writing slot `o` keeps every other slot but the
temporary area's (`sv_keep`) and the moduli (`ModOkW.keepArm`).
-/

namespace VG.Proof.Ecdsa.Arm

open VG VG.Arm VG.Impl.Mont.Arm VG.Impl.Mont VG.Impl.Weierstrass.Arm VG.Impl.Weierstrass
open VG.Impl.Ecdsa.Arm
open VG.Proof.Mont.Arm VG.Proof.Mont VG.Proof.Weierstrass.Arm VG.Proof.Weierstrass Spec.Weierstrass

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
    (h : ProgKeep M base c.wk [c.sl o] s s') {i : Nat} (hi : i < 45) (hio : i ≠ o) (hit : i ≠ TMP) :
    sv c base s' i = sv c base s i := by
  have hl := sl_le c h7 hi
  have hk := sl_below_wk c h7 hi
  refine h.unchOne.wordsVal (fun w hw => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · rw [hMn]; exact sl_apart c hio
  · rw [hMn, hMt]; exact sl_apart c hit
  · exact .inl hk

/-- The modulus in slot `j` survives an operation writing another slot. -/
theorem _root_.VG.Proof.Mont.ModOkW.keepArm {M M' : Mod} {m : Nat} {base : Addr} {s s' : State}
    (hM : ModOkW M size m s.mem base) {j : Nat} (hj : j < 45) (hmo : M.mo = c.sl j) (hMn : M.n = c.n)
    (hM'n : M'.n = c.n) (hM't : M'.tmp = c.sl TMP) (h7 : c.n < 10) (hn : base.toNat + size ≤ 2 ^ 32)
    {o : Nat} (h : ProgKeep M' base c.wk [c.sl o] s s') (hjo : j ≠ o) (hjt : j ≠ TMP) :
    ModOkW M size m s'.mem base :=
  ⟨hM.n0, hM.mo, hM.tmp, hM.sep, by
    have := sv_keep hM'n hM't h7 hn h hj hjo hjt
    simp only [sv] at this
    rw [hmo, hMn, this, ← hMn, ← hmo]; exact hM.val, hM.inv, hM.red⟩

/-- A slot, in the functions' terms. -/
theorem slFits {M : Mod} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M c.wk S m)
    (hMn : M.n = c.n) (h7 : c.n < 10) {i : Nat} (hi : i < 45) :
    c.sl i + 8 * S.k ≤ Impl.Weierstrass.Arm.Mont.own S.k :=
  hF.fits (by rw [hMn]; exact sl_below_wk c h7 hi)

/-- `[o] = [a] [b] R⁻¹ mod m`, on slots. -/
theorem slMul_ok {M : Mod} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M c.wk S m)
    (hMn : M.n = c.n) (h7 : c.n < 10) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45) (hB : sv c base s b < m) :
    WP isa (Mont.mulCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => ProgKeep M base c.wk [c.sl o] s s' ∧
      sv c base s' o < m ∧ sv c base s' o * 2 ^ (64 * c.n) % m = sv c base s a * sv c base s b % m := by
  refine WP.mono (Mont.mulCall_ok hF.ok hs hf (slFits hF hMn h7 ho) (slFits hF hMn h7 ha) (slFits hF hMn h7 hb)
    (by rw [hF.k, hF.m, hMn]; exact hB)) fun s' ⟨K, lt, e⟩ => ?_
  rw [hF.k, hF.m, hMn] at lt e
  exact ⟨.of_call hF K, lt, e⟩

/-- `[o] = ([a] + [b]) mod m`, on slots. -/
theorem slAdd_ok {M : Mod} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M c.wk S m)
    (hMn : M.n = c.n) (h7 : c.n < 10) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hAB : sv c base s a + sv c base s b < 2 * m) :
    WP isa (Mont.addCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => ProgKeep M base c.wk [c.sl o] s s' ∧
      sv c base s' o = (sv c base s a + sv c base s b) % m := by
  refine WP.mono (Mont.addCall_ok hF.ok hs hf (slFits hF hMn h7 ho) (slFits hF hMn h7 ha) (slFits hF hMn h7 hb)
    (by rw [hF.k, hF.m, hMn]; exact hAB)) fun s' ⟨K, e⟩ => ?_
  rw [hF.k, hF.m, hMn] at e
  exact ⟨.of_call hF K, e⟩

/-- `[o] = ([a] - [b]) mod m`, on slots. -/
theorem slSub_ok {M : Mod} {S : Spec.Weierstrass.Mont.Modulus} {m : Nat} (hF : FnOk M c.wk S m)
    (hMn : M.n = c.n) (h7 : c.n < 10) {base : Addr} {s : State} (hs : Scr s base size)
    (hf : Far s base 8192) {o a b : Nat} (ho : o < 45) (ha : a < 45) (hb : b < 45)
    (hA : sv c base s a < m) (hB : sv c base s b < m) :
    WP isa (Mont.subCall S (c.sl o) (c.sl a) (c.sl b)) s fun s' => ProgKeep M base c.wk [c.sl o] s s' ∧
      sv c base s' o = (sv c base s a + m - sv c base s b) % m := by
  refine WP.mono (Mont.subCall_ok hF.ok hs hf (slFits hF hMn h7 ho) (slFits hF hMn h7 ha) (slFits hF hMn h7 hb)
    (by rw [hF.k, hF.m, hMn]; exact hA) (by rw [hF.k, hF.m, hMn]; exact hB)) fun s' ⟨K, e⟩ => ?_
  rw [hF.k, hF.m, hMn] at e
  exact ⟨.of_call hF K, e⟩

end VG.Proof.Ecdsa.Arm
