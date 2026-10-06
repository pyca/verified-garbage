import VerifiedGarbage.Proof.Weierstrass.AArch64.JacWindowStepTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem jacLoop_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits+5≤4096)
    (hk : 16*Window5.geom 52≤k) (hklt : k<32^52) (hc : JacStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (JacPair K C base size P k 0 52)
      (.loop (Jacobian.jacStep K 5) (.nonzero .x .x19))
      (JacPair K C base size P k (k-16*Window5.geom 52) 0) := by
  let I := fun j s t => 1≤j ∧ j≤52 ∧ JacPair K C base size P k (Window5.winE k 52 j) j s t
  have step : ∀ j, RelCT isa (I j) (Jacobian.jacStep K 5) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → JacPair K C base size P k (k-16*Window5.geom 52) 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj52 : j≤52
      · refine (jacStep_relCT hL hJ hAl hm hC ha hOne hTbl hBits hk (j:=j-1) (by omega) hc hP).mono
          (P':=I j) (fun _ _ h => by simpa only [Nat.sub_add_cancel hj] using h.2.2) ?_
        intro s t hp
        have s19 := hp.2.2.2.1
        have t19 := hp.2.2.2.2
        refine ⟨by simp only [eval,State.read,s19,t19],fun he => ?_,fun he => ?_⟩
        · have hz : j-1=0 := by
            by_contra hn
            have hb : (BitVec.ofNat 64 (j-1) != 0)=true := by
              rw [bne_iff_ne]
              intro hh
              have hh' := congrArg BitVec.toNat hh
              simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : j-1<2^64)] at hh'
              exact hn hh'
            have htrue : eval (.nonzero .x .x19) s=some true := by
              change some (s.read .x .x19 != 0)=some true
              rw [read_x,s19,hb]
            rw [htrue] at he; cases he
          simpa only [hz,Window5.winE_zero] using hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj52 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 52).mono (fun _ _ h => ⟨by decide,by decide,by
    simpa only [Window5.winE_top hklt] using h⟩) (fun _ _ h => h)

end VG.Proof.Weierstrass.AArch64
