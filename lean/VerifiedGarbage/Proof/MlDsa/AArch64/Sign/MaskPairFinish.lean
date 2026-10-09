import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.MaskPairSeed

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.Sign VG.Spec.MlDsa

def maskFinishChk (p : Params) (n r : Nat) : Bool :=
  let y := pS (yBase p+r)
  let yh := pS (yhBase p+r)
  copyChk (sgR p) (sgW p) yh y 1024 &&
  icmChk p [(yh,1024)] r && famChk (sgR p) (sgW p) [(yh,1024)] (yBase p) n &&
  ipChkS (sgR p) (sgW p) yh && icmChk p [(yh,1024),(sc oPS,1024)] r &&
  famChk (sgR p) (sgW p) [(yh,1024),(sc oPS,1024)] (yBase p) n

/-- Copy and transform one already sampled mask, keeping both canonical
outputs of the paired sampler available for the rejection checks. -/
theorem maskFinish_ok {P : Prims} {D : Nat} (hP : PrimsOk P D)
    {p : Params} {σ s : State} {t n r : Nat} (hr : r<n)
    (hc : maskFinishChk p n r=true) (h : ICm p D σ t r s)
    (hy : Fam s (yBase p) n (Yv p σ (p.ℓ*t))) :
    WP isa (maskFinish P p r) s fun u => ICm p D σ t (r+1) u ∧
      Fam u (yBase p) n (Yv p σ (p.ℓ*t)) := by
  simp only [maskFinishChk,Bool.and_eq_true,and_assoc] at hc
  obtain ⟨cc,c1,fy1,ci,c2,fy2⟩ := hc
  unfold maskFinish
  refine WP.seq (WP.mono (copy_ok h.l.st.lay cc) fun a ⟨ha,_,hb⟩ => ?_)
  have hA := h.step ha c1
  have hya := Fam.keep h.l.st.lay ha fy1 hy
  have hpoly : Pl a (yhBase p+r) (Yv p σ (p.ℓ*t) r) := by
    show PolyIs _ _ _
    rw [ha.pa (pS_bases _)]
    exact polyIs_of_bytes hb (hy r hr)
  refine WP.mono (ipAt_ok (t := ntt) hP.ntt hA.l.st.lay ci hpoly.1)
    fun u ⟨hu,_,hqu⟩ => ?_
  have hU := hA.step hu c2
  have hyu := Fam.keep hA.l.st.lay hu fy2 hya
  refine ⟨⟨hU.l,fun i hi => hyu i (by omega),Fam.snoc hU.yh ?_⟩,hyu⟩
  show PolyIs _ _ _
  rw [hu.pa (pS_bases _),hpoly.2] at *
  exact hqu

end VG.Proof.MlDsa.AArch64.Sign
