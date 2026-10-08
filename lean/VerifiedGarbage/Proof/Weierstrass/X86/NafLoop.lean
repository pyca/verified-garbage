import VerifiedGarbage.Proof.Weierstrass.X86.NafStep

/-! The 256 counted Jacobian iterations and the extra carry digit at bit 256. -/
namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
  VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLoop_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) (Naf5.residual k 256) s)
    (hc : s.gpr .esi=256) :
    WP isa (.loop (Naf.windowStep K F) .ne) s fun t =>
      NafLoopKeep K base wk s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .esi=0 := by
  let I := fun j t => NafLoopKeep K base wk s t ∧
    NafCore K C base size P (Naf5.byte k) (Naf5.residual k j) t ∧ t.gpr .esi=BitVec.ofNat 32 j
  apply countLoop_ok (Inv:=I) (n:=256)
  · intro j a hj1 hj256 hi
    obtain ⟨ka,ca,ac⟩ := hi
    have he : j-1+1=j := by omega
    have cp : NafCore K C base size P (Naf5.byte k) (Naf5.residual k (j-1+1)) a := he.symm ▸ ca
    have ap : a.gpr .esi=BitVec.ofNat 32 (j-1+1) := he.symm ▸ ac
    refine WP.mono (nafStep_ok hL hJ hAcc hBitsWk hm hC ha hOne (by omega) hP cp ap)
      fun t ⟨kt,ct,tc,tz⟩ => ⟨⟨ka.trans kt,ct,tc⟩,tz⟩
  · intro t ht
    obtain ⟨kt,ct,tc⟩ := ht
    exact ⟨kt,ct,tc⟩
  · decide
  · exact ⟨NafLoopKeep.refl K base wk s,h,hc⟩

theorem nafRun_ok {F : Spec.Weierstrass.Mont.Modulus} {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat}
    (hL : NafLay K size) (hJ : K.J=65) (hAcc : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk)
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hk : k<2^256) {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : NafCore K C base size P (Naf5.byte k) 0 s) (hc : s.gpr .esi=256) :
    WP isa (.seq (Naf.digit K F) (.loop (Naf.windowStep K F) .ne)) s fun t =>
      NafLoopKeep K base wk s t ∧ NafCore K C base size P (Naf5.byte k) k t ∧ t.gpr .esi=0 := by
  have he : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
  apply WP.seq
  refine WP.mono (nafDigit_ok hL hJ hAcc hBitsWk hm hC ha hOne (by decide) hP (he.symm ▸ h) hc)
    fun a ⟨ka,ca⟩ => ?_
  have ac : a.gpr .esi=256 := (ka.gpr _ (by decide)).trans hc
  refine WP.mono (nafLoop_ok hL hJ hAcc hBitsWk hm hC ha hOne hP ca ac)
    fun t ⟨kt,ct,tc⟩ => ⟨?_,ct,tc⟩
  have kp : NafLoopKeep K base wk s a :=
    ⟨Keeps.mono ⟨ka.gpr,ka.rd,ka.wr⟩ (fun _ hr => List.mem_append_left _ hr),ka.unch⟩
  exact kp.trans kt

end VG.Proof.Weierstrass.X86
