import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStep

/-! The 52-iteration signed-window loop, without coordinate conversions. -/
namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass

/-- All 52 signed windows reconstruct the original scalar after subtracting
the offset used by the caller. -/
theorem jacLoop_ok {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (· ∈ jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hklt : k<32^52)
    {P : Point C} (hP : onCurve C P=true) {s : State}
    (h : JacCore K C base size P k 0 s) (h19 : s.gpr .x19=BitVec.ofNat 64 52) :
    WP isa (.loop (Jacobian.jacStep K 5) (.nonzero .x .x19)) s fun t =>
      JacLoopKeep K base s t ∧ JacCore K C base size P k (k-16*Window5.geom 52) t ∧
      t.gpr .x19=0 := by
  let I := fun j t => JacLoopKeep K base s t ∧
    JacCore K C base size P k (Window5.winE k 52 j) t ∧ t.gpr .x19=BitVec.ofNat 64 j
  apply countLoop_ok (Inv := I) (n := 52) (by decide)
  · intro j a hj1 hj52 hi
    obtain ⟨ka,ca,a19⟩ := hi
    have hj : j-1<52 := by omega
    have hidx : j-1+1=j := by omega
    have cp : JacCore K C base size P k (Window5.winE k 52 (j-1+1)) a := hidx.symm ▸ ca
    have ap : a.gpr .x19=BitVec.ofNat 64 (j-1+1) := hidx.symm ▸ a19
    refine WP.mono (jacStep_ok hL hJ hAl hm hC ha hOne hTbl hBits hk hj hP cp ap)
      fun t ⟨kt,ct,t19⟩ => ⟨⟨ka.trans kt,ct,t19⟩,t19⟩
  · intro t ht
    obtain ⟨kt,ct,t19⟩ := ht
    rw [Window5.winE_zero] at ct
    exact ⟨kt,ct,t19⟩
  · decide
  · exact ⟨JacLoopKeep.refl K base s,by rw [Window5.winE_top hklt]; exact h,h19⟩

end VG.Proof.Weierstrass.AArch64
