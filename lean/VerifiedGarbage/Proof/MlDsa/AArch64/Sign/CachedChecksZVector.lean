import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksZ

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedZ_rooted_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r<p.ℓ) (roots : Roots p S f s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) s (fun u => PositiveIZ p S σ t (r+1) u ∧ Roots p S f u) := by
  have hc := optimizedZChk_ok hp r hr
  simp only [optimizedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyr,hcr⟩,hyw⟩,hsep⟩,hb⟩,zp⟩,yp⟩,zz⟩,yz⟩,ze⟩,ye⟩,hwp⟩ := hc
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_z hp r hr) h.b.c (h.b.l.k.d.s1 r hr)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hwp (keep_product hp)
  have ha := h.step hpa hsa zp yp hwp
  have hy : PolyIs a.mem (pa a (yP p r)) (Yv p σ (p.ℓ*t) r) := by
    have hv := ha.y 0 (by omega)
    simpa only [Nat.add_zero] using hv
  have hraw : RawPolyIs a.mem (pa a t1P)
      (nttInv (multiplyNTT (VG.Proof.MlDsa.Sign.chF (cV p σ (p.ℓ*t))) (S1v p σ r))) := by
    rw [hpa.pa (by decide)]; exact hprod
  have ready := addNormReady_layout ha.b.l.st.lay hyr hcr hyw hsep hy.1 hraw.1 hb.1 hb.2
  refine WP.seq (WP.mono_syms (addNormAt_field_layout ha.b.l.st.lay hyr hcr ready hy hraw)
    fun b ⟨hpb,h24b,hz,hret⟩ hsb => ?_)
  have rb := ra.step_layout ha.b.l.st.lay hpb hsb (by
    intro w hw; simp only [List.mem_singleton] at hw; subst w; exact hyw) (keep_z hp hr)
  have hz' : SignedPl b (yBase p+r) (Zv p σ (p.ℓ*t) r) (-(q:Int)+1) ((q:Int)-1) := by
    change SignedPolyIs b.mem (pa b (yP p r)) _ _ _
    rw [hpb.pa (ha.b.l.st.lay.ptrBs hyr)]
    exact hz
  simp only [zfam,Bool.and_eq_true] at zz
  have hbstate : PositiveIZb p S σ t (r+1) b :=
    ⟨ha.b.step hpb hsb zz.1.1.1 (by simpa using hyw),
      (ha.z.keep ha.b.l.st.lay hpb zz.1.1.2).snoc hz',
      (ha.y.shift hr).keep ha.b.l.st.lay hpb yz,
      ha.w.keep ha.b.l.st.lay hpb zz.1.2,(ha.b.l.st.lay.keepW hpb zz.2).trans ha.ones⟩
  refine WP.mono_syms (and24_ok b) fun c ⟨hkc,hflagc⟩ hsc => ?_
  have hpc : PPostB S b c [] := postB24 hkc []
  refine ⟨⟨hbstate.step hpc hsc ze ye (by simp),?_⟩,
    rb.step_layout hbstate.b.l.st.lay hpc hsc (by simp) (keep_nil hp)⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr forall_lt_succ

theorem optimizedZ_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : Roots p S f s) (h : PositiveIZ p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector p) s fun u =>
      PositiveIZ p S σ t p.ℓ u ∧ Roots p S f u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector
  refine WP.seq (WP.mono (seqR_ok (I:=fun j s => PositiveIZ p S σ t (2*j) s ∧ Roots p S f s)
    (p.ℓ/2) 0 (fun j _ hj a ha => ?_) s ⟨by simpa only [Nat.mul_zero] using h,roots⟩) ?_)
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedZ_pair_ok hp (by omega : 2*j+1<p.ℓ) ha.2 ha.1
  · intro a ha
    simp only [Nat.zero_add] at ha
    split
    · rename_i hodd
      have he : 2*(p.ℓ/2)=p.ℓ-1 := by omega
      have hend : p.ℓ-1+1=p.ℓ := by omega
      rw [he] at ha
      simpa only [hend] using optimizedZ_rooted_ok hp (by omega : p.ℓ-1<p.ℓ) ha.2 ha.1
    · rename_i heven
      have he : 2*(p.ℓ/2)=p.ℓ := by omega
      rw [he] at ha
      exact WP.block_nil ha

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks
