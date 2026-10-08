import VerifiedGarbage.Proof.Weierstrass.X86.NafStepTiming

namespace VG.Proof.Weierstrass.X86
open VG VG.X86 VG.Impl.Mont VG.Impl.Weierstrass VG.Impl.Weierstrass.X86
open VG.Proof.Mont VG.Proof.Mont.X86 Spec.Weierstrass

theorem nafLoop_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k 256) 256)
      (.loop (Naf.windowStep K F) .ne)
      (NafRunPair K C base size P (Naf5.byte k) k 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧
    NafRunPair K C base size P (Naf5.byte k) (Naf5.residual k j) (BitVec.ofNat 32 j) s t
  have step : ∀ j,RelCT isa (I j) (Naf.windowStep K F) (fun s t =>
      eval .ne s=eval .ne t ∧
      (eval .ne s=some false → NafRunPair K C base size P (Naf5.byte k) k 0 s t) ∧
      (eval .ne s=some true → ∃ n<j,I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (nafStep_relCT hL hJ hW hBitsWk hm hC ha hOne (j:=j-1) (by omega) hP hc).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t ⟨hp,cs,ct⟩
        have es : eval .ne s=some (!decide (j-1=0)) := by simp only [eval,cs,Option.map_some]
        have et : eval .ne t=some (!decide (j-1=0)) := by simp only [eval,ct,Option.map_some]
        refine ⟨es.trans et.symm,fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            have := Option.some.inj (es.symm.trans he)
            simpa using this
          rw [hz] at hp
          exact hp
        · have hz : j-1≠0 := by
            have := Option.some.inj (es.symm.trans he)
            simpa using this
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 256).mono (fun _ _ h => ⟨by decide,by decide,h⟩) (fun _ _ h => h)

theorem nafRun_relCT {F : Spec.Weierstrass.Mont.Modulus}
    {K : WinCfg} {C : Curve} {base : Addr} {size wk k : Nat} {P : Point C}
    (hL : NafLay K size) (hJ : K.J=65) (hW : WkOk F K.M C.p size wk (·∈nafSlots K))
    (hBitsWk : K.bits+260≤wk) (hm : UnitMod C.p (2^(64*K.M.n)))
    (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p) (hk : k<2^256) (hP : onCurve C P=true)
    (hc : NafStepChecks K F) :
    RelCT isa (NafRunPair K C base size P (Naf5.byte k) 0 256)
      (.seq (Naf.digit K F) (.loop (Naf.windowStep K F) .ne))
      (NafRunPair K C base size P (Naf5.byte k) k 0) := by
  have hd := nafDigit_relCT (base:=base) (k:=k) (j:=256) hL hJ hW hBitsWk hm hC ha hOne (by decide) hP hc.digit
  rw [Naf5.residual_zero257 hk,Nat.mul_zero] at hd
  exact hd.seq (nafLoop_relCT hL hJ hW hBitsWk hm hC ha hOne hP hc)

end VG.Proof.Weierstrass.X86
