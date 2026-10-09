import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairFinish

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)

def maskPairStepChk (p : Params) (r : Nat) : Bool :=
  pairSeedChk p r 0 && pairSeedChk p r 1 &&
  keepB (sgR p) (sgW p) (pairSeedWrites 1) (sc oMP) 66 &&
  maskPairChk (sgR p) (sgW p) (sc oMP) (yP p r) (yP p (r+1)) (sc (oR4 p)) &&
  icmChk p [(yP p r,1024),(yP p (r+1),1024),(sc (oR4 p),8192)] r &&
  maskFinishChk p (r+2) r && maskFinishChk p (r+2) (r+1) &&
  decide (p.γ₁=2^17 ∨ p.γ₁=2^19)

/-- Paired expansion advances the same canonical and transformed mask
invariants by two, with the original per-polynomial seeds. -/
theorem maskPairR_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {nm : String} {cd : Prog isa} (C : CalleeOk D cd (expandMaskPairContract AArch64.abi D))
    {p : Params} {σ s : State} {t r : Nat} (hc : maskPairStepChk p r=true)
    (h : ICm p D σ t r s) :
    WP isa (maskPairR P p nm cd r) s (ICm p D σ t (r+2)) := by
  simp only [maskPairStepChk,Bool.and_eq_true,and_assoc,decide_eq_true_eq] at hc
  obtain ⟨cs0,cs1,ck,cm,ci,cf0,cf1,hg⟩ := hc
  unfold maskPairR
  refine WP.seq (WP.mono (maskPairSeed_ok cs0 h) fun a ⟨hA,_,ha⟩ => ?_)
  refine WP.seq (WP.mono (maskPairSeed_ok cs1 hA) fun b ⟨hB,hb,hseed1⟩ => ?_)
  have hseed0 : bytesAt b.mem (pa b (sc oMP)) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+r) 2 := by
    have hkeep := hA.l.st.lay.keepBytes hb ck
    simp only [Nat.mul_zero,Nat.add_zero] at ha
    rw [hkeep]
    exact ha
  have hseed1' : bytesAt b.mem (pa b (sc oMP)+66) 66=
      rppOf p σ++integerToBytes (p.ℓ*t+(r+1)) 2 := by
    change bytesAt b.mem (pa b (sc (oMP+66))) 66=_ at hseed1
    rw [← pa_sc_add] at hseed1
    exact hseed1
  refine WP.seq (WP.mono (maskPairAt_ok hB.l.st.lay.s64 C hB.l.st.lay cm hg)
    fun c ⟨hcP,_,hy0,hy1⟩ => ?_)
  rw [hseed0] at hy0
  rw [hseed1'] at hy1
  have hC := hB.step hcP ci
  have hy : Fam c (yBase p) (r+2) (Yv p σ (p.ℓ*t)) := by
    refine Fam.snoc (Fam.snoc hC.y ?_) ?_
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy0
    · show PolyIs _ _ _
      rw [hcP.pa (pS_bases _)]
      exact hy1
  refine WP.seq (WP.mono (maskFinish_ok hP (by omega) cf0 hC hy) fun d ⟨hD,hyD⟩ => ?_)
  exact WP.mono (maskFinish_ok hP (by omega) cf1 hD hyD) fun _ hu => hu.1

end VG.Proof.MlDsa.AArch64.Sign
