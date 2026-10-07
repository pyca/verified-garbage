import VerifiedGarbage.Proof.Weierstrass.AArch64.NafStepTiming

namespace VG.Proof.Weierstrass.AArch64
open VG VG.AArch64 VG.Impl.Mont.AArch64 VG.Impl.Mont VG.Impl.Weierstrass.AArch64 VG.Impl.Weierstrass
open VG.Proof.Mont.AArch64 VG.Proof.Mont Spec.Weierstrass
open VG.Proof.Ed25519.AArch64 (read_x)

theorem nafLoop_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096)
    (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k (Naf5.residual k 256) 256)
      (.loop (Naf.step K) (.nonzero .x .x19))
      (NafPair K C base size P k k 0) := by
  let I := fun j s t => 1≤j ∧ j≤256 ∧ NafPair K C base size P k (Naf5.residual k j) j s t
  have step : ∀ j, RelCT isa (I j) (Naf.step K) (fun s t =>
      eval (.nonzero .x .x19) s=eval (.nonzero .x .x19) t ∧
      (eval (.nonzero .x .x19) s=some false → NafPair K C base size P k k 0 s t) ∧
      (eval (.nonzero .x .x19) s=some true → ∃ n<j, I n s t)) := by
    intro j
    by_cases hj : 1≤j
    · by_cases hj256 : j≤256
      · refine (nafStep_relCT hL hJ hAl hm hC ha hOne hTbl hBits (j:=j-1) (by omega) hc hP).mono
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
          simpa only [hz,Naf5.residual_zero] using hp
        · have hz : j-1≠0 := by
            intro hz; simp only [eval,State.read,s19,hz] at he; cases he
          exact ⟨j-1,by omega,by omega,by omega,hp⟩
      · exact RelCT.of_false (fun _ _ h => hj256 h.2.1)
    · exact RelCT.of_false (fun _ _ h => hj h.1)
  exact (RelCT.loop I step 256).mono (fun _ _ h => ⟨by decide,by decide,by
    exact h⟩) (fun _ _ h => h)


theorem nafRun_relCT {K : WinCfg} {C : Curve} {base : Addr} {size k : Nat}
    (hL : JacWinLay K size) (hJ : K.J=52) (hAl : Aligned K.M (·∈jacWinSlots K))
    (hm : UnitMod C.p (2^(64*K.M.n))) (hC : Law C) (ha : AM3 C) (hOne : K.one<C.p)
    (hTbl : K.tbl<4096) (hBits : K.bits<4096) (hk : k<2^256) (hc : NafStepChecks K)
    {P : Point C} (hP : onCurve C P=true) :
    RelCT isa (NafPair K C base size P k 0 256)
      (.seq (Naf.digit K) (.loop (Naf.step K) (.nonzero .x .x19)))
      (NafPair K C base size P k k 0) := by
  have seed : RelCT isa (NafPair K C base size P k 0 256) (Naf.digit K)
      (NafPair K C base size P k (Naf5.residual k 256) 256) := by
    intro s t ts tt s' t' ⟨⟨E,hp⟩,cs,ct,ps,pt⟩ es et
    obtain ⟨he,E',pair⟩ := nafDigit_relCT hL hJ hAl hm hOne hTbl hBits (by decide) hc.digit
      _ _ _ _ _ _ ⟨hp,cs,ct,ps,pt⟩ es et
    have hz : 2*Naf5.residual k (256+1)=0 := by rw [Naf5.residual_zero257 hk,Nat.mul_zero]
    obtain ⟨_,_,xs,ks,cs'⟩ := nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (hz.symm ▸ cs) ps
    obtain ⟨_,_,xt,kt,ct'⟩ := nafDigit_ok hL hJ hAl hm hC ha hOne hTbl hBits (by decide) hP (hz.symm ▸ ct) pt
    obtain ⟨_,rfl⟩ := Exec.det es xs
    obtain ⟨_,rfl⟩ := Exec.det et xt
    exact ⟨he,⟨E',pair⟩,cs',ct',(ks.gpr _ (x19_not_clob _)).trans ps,
      (kt.gpr _ (x19_not_clob _)).trans pt⟩
  exact RelCT.seq seed (nafLoop_relCT hL hJ hAl hm hC ha hOne hTbl hBits hc hP)

end VG.Proof.Weierstrass.AArch64
