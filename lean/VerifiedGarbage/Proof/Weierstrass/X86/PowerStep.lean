import VerifiedGarbage.Proof.Weierstrass.X86.PowerState

/-! # Multiplication and saved powers in fixed exponentiation chains -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.X86.Wp VG.Impl.Mont.X86 VG.Impl.Mont VG.Impl.Weierstrass.X86 VG.Impl.Weierstrass
  VG.Proof.Mont.X86 VG.Proof.Mont VG.Proof.Weierstrass

theorem powerMul_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t b e : Nat}
    [NeZero m] {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) (hm : UnitMod m (2 ^ (64 * P.M.n)))
    (hbw : b + 8 * P.M.n ≤ wk)
    (hblt : wordsVal s.mem base b P.M.n < m)
    (hbval : toM m (2 ^ (64 * P.M.n)) (wordsVal s.mem base b P.M.n) = B ^ e) :
    WP isa (Mont.mulCall F P.acc P.acc b) s fun u =>
      PowerState P base size m B (a + e) t u ∧ Keeps clob s u ∧
      Unch base (powWx P wk) s.mem u.mem := by
  have hn := I.scr.nowrap
  have htmp := hL.tmp
  refine WP.mono (mulC_ok hW.toCallCfg I.scr hW.acc hW.acc hbw hblt) fun u ⟨K, L, V⟩ => ?_
  have U : Unch base (powWx P wk) s.mem u.mem := K.unch.mono fun w hw => by
    simp only [powWx, powW, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
    grind
  have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.tmp P.M.n :=
    K.unch.wordsVal (fun w hw => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact hL.acc_tmp.symm
      · exact hL.tmp_mtmp
      · exact .inl hW.tmp
      · have := hW.tmp; have := hW.toCallCfg.own_le
        exact .inl (by simp only; omega)) (by omega)
  refine ⟨I.rebuild hL hW (K.scr I.scr) U L ?_ (et ▸ I.tmp_lt) ?_, ⟨K.gpr, K.rd, K.wr⟩, U⟩
  · rw [toM_mul hm V, I.acc_val, hbval, Lean.Grind.Semiring.pow_add]
  · rw [et]; exact I.tmp_val

theorem powerSave_ok {P : PowCfg} {F : Spec.Weierstrass.Mont.Modulus} {base : Addr} {size wk m a t : Nat}
    [NeZero m] {B : Fin m} {s : State} (I : PowerState P base size m B a t s)
    (hL : PowLay P size) (hW : PowWk P F m size wk) :
    WP isa (.block (copy (2 * P.M.n) P.tmp P.acc)) s fun u =>
      PowerState P base size m B a a u ∧ Keeps [.eax] s u ∧ Unch base (powWx P wk) s.mem u.mem := by
  have hn := I.scr.nowrap
  have ha := hL.acc
  have ht := hL.tmp
  have hap := hL.acc_tmp
  refine WP.mono (copy_ok (2 * P.M.n) I.scr (o := P.tmp) (a := P.acc) (by omega) (by omega) (by omega))
    fun u ⟨V, K, O⟩ => ?_
  rw [show 4 * (2 * P.M.n) = 8 * P.M.n by omega] at O
  have U : Unch base (powWx P wk) s.mem u.mem := O.unch.mono fun w hw => by
    simp only [List.mem_singleton] at hw
    simp [hw, powWx, powW]
  have et : wordsVal u.mem base P.tmp P.M.n = wordsVal s.mem base P.acc P.M.n := by
    rw [wordsVal_eq_val32, V, ← wordsVal_eq_val32]
  have ea : wordsVal u.mem base P.acc P.M.n = wordsVal s.mem base P.acc P.M.n :=
    O.wordsVal hap (by omega)
  refine ⟨I.rebuild hL hW (I.scr.of_keeps K (by decide)) U (ea ▸ I.acc_lt) ?_ (et ▸ I.acc_lt) ?_, K, U⟩
  · rw [ea]; exact I.acc_val
  · rw [et]; exact I.acc_val

end VG.Proof.Weierstrass.X86
