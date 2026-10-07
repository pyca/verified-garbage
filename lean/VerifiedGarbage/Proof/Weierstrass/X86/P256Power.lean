import VerifiedGarbage.Proof.Weierstrass.X86.PowerChain

/-! # P-256 field inversion by a fixed addition chain -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem powerInit_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) {s : State} (hs : Scr s base size)
    (hM : ModOkW P.M size m s.mem base) (hB : wordsVal s.mem base P.base P.M.n < m) :
    WP isa (.block (copy (2 * P.M.n) P.acc P.base ++ copy (2 * P.M.n) P.tmp P.base)) s fun u =>
      PowerState P base size m
        (toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n)) 1 1 u ∧
      Keeps [.eax] s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  have hn := hs.nowrap
  have ha := hL.acc
  have ht := hL.tmp
  have hb := hL.base
  have hmo := hM.mo
  have hba := hL.base_w (P.acc, 8 * P.M.n) (by simp [powW])
  have hbt := hL.base_w (P.tmp, 8 * P.M.n) (by simp [powW])
  refine WP.block_append (WP.mono (copy_ok (2 * P.M.n) hs (o := P.acc) (a := P.base)
    (by omega) (by omega) (by omega)) fun s₁ ⟨V₁, K₁, O₁⟩ => ?_)
  have hs₁ := hs.of_keeps K₁ (by decide)
  refine WP.mono (copy_ok (2 * P.M.n) hs₁ (o := P.tmp) (a := P.base)
    (by omega) (by omega) (by omega)) fun u ⟨V₂, K₂, O₂⟩ => ?_
  rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega] at O₁ O₂
  have U : Unch base (powWx P wk) s.mem u.mem := by
    intro x hx
    rw [O₂ x (hx (P.tmp, 8 * P.M.n) (by simp [powWx, powW])),
      O₁ x (hx (P.acc, 8 * P.M.n) (by simp [powWx, powW]))]
  have eb₁ := O₁.wordsVal hba (by omega)
  have ea : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base P.base P.M.n := by
    rw [O₂.wordsVal hL.acc_tmp (by omega), wordsVal_eq_val32, V₁, ← wordsVal_eq_val32]
  have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.base P.M.n := by
    rw [wordsVal_eq_val32, V₂, ← wordsVal_eq_val32, eb₁]
  have eb := U.wordsVal (powWx_base hL hW) (by omega)
  have em := U.wordsVal (powWx_mo hL hW) (by omega)
  refine ⟨⟨hs₁.of_keeps K₂ (by decide),
    ⟨hM.n0, hM.mo, hM.tmp, hM.sep, em.trans hM.val, hM.inv, hM.red⟩,
    eb ▸ hB, ?_, ea ▸ hB, ?_, et ▸ hB, ?_⟩, K₁.trans K₂, U⟩
  · rw [eb]
  · rw [ea, Lean.Grind.Semiring.pow_one]
  · rw [et, Lean.Grind.Semiring.pow_one]

theorem p256Power_exponent : chainExponents p256PowerOps (1, 1) = (p256Prime - 2, 2 ^ 30 - 1) := by
  decide +kernel

theorem p256Power_bound : ∀ op ∈ p256PowerOps, powerOpBound op := by
  simp only [p256PowerOps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
    powerOpBound]
  decide +kernel

theorem p256Power_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m) :
    WP isa (p256Power P wk) s fun u => Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem ∧
      wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (p256Prime - 2) := by
  refine WP.seq (WP.mono (powerInit_ok hL hW hs hM hB) fun s₁ ⟨I₁, K₁, U₁⟩ => ?_)
  refine WP.mono (powerChain_ok hL hW hm p256PowerOps p256Power_bound (v := (1, 1)) I₁) fun u ⟨Iu, Ku, Uu⟩ => ?_
  rw [p256Power_exponent] at Iu
  exact ⟨(K₁.mono (by decide)).trans Ku, fun x hx => (Uu x hx).trans (U₁ x hx), Iu.acc_lt, Iu.acc_val⟩

theorem powField_ok {P : PowCfg} {base : Addr} {size wk m : Nat} [NeZero m]
    (hL : PowLay P size) (hW : PowWk P size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    {s : State} (hs : Scr s base size) (hM : ModOkW P.M size m s.mem base)
    (hB : wordsVal s.mem base P.base P.M.n < m)
    (hO : wordsVal s.mem base P.one P.M.n = 2 ^ (64 * P.M.n) % m)
    (hbits : ∀ t < P.nbits, s.mem (off base (P.bits + t)) = if (m - 2).testBit t then 1 else 0)
    (he : m - 2 < 2 ^ P.nbits) :
    WP isa (powField P wk m) s fun u => Keeps powClob s u ∧ Unch base (powWx P wk) s.mem u.mem ∧
      wordsVal u.mem base P.acc P.M.n < m ∧
      toM m (2 ^ (64 * P.M.n)) (wordsVal u.mem base P.acc P.M.n) =
        toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base P.base P.M.n) ^ (m - 2) := by
  unfold powField
  split
  next hp =>
    exact WP.mono (p256Power_ok hL hW hm hs hM hB) fun u ⟨K, U, L, V⟩ =>
      ⟨K, U, L, by rw [← hp] at V; exact V⟩
  next _ => exact pow_ok hL hW hm hs hM hB hO hbits he

end VG.Proof.Weierstrass.X86
