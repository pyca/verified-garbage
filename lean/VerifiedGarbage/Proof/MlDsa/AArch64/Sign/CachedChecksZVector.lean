import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.CachedChecksBase

/-! ## From `CachedChecksZ.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign.CachedChecks
variable {f : VG.Spec.MlDsa.Poly}
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedZ_pair_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r+1<p.ℓ) (roots : Roots p S f s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) s fun u =>
      PositiveIZ p S σ t (r+2) u ∧ Roots p S f u := by
  have checks := pairedZChk_ok hp r (by omega) hr
  simp only [pairedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hy⟩,hw⟩,hwy⟩,hww⟩,hcy⟩,hcw⟩,hsy⟩,hsw⟩,hyw⟩,hB⟩,hz⟩,hys⟩,he⟩,hye⟩,hws⟩ := checks
  obtain ⟨h,hflag⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (yP p r)) j) (Yv p σ (p.ℓ*t) (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.y j (by omega)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s1P p r)) j) (S1v p σ (r+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s1 (r+j) (by omega)
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s1P p r)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hsum : ∀j<2,add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j))
      (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j)=Zv p σ (p.ℓ*t) (r+j) := by
    intro j hj
    rw [(hdata j hj).2]
    simp only [pairedProduct,h.b.c.value,(hsecret j hj).value]
    rfl
  have ready := pairedZReady_layout h.b.l.st.lay roots.roots hc hs hy hw hwy hww hcy hcw hsy hsw hyw
    hprod (fun j hj => (hdata j hj).1) hB.1 hB.2
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPair
  refine WP.seq (WP.mono_syms (pairedZAt_layout (gamma:=p.γ₁) h.b.l.st.lay hc hs hy hw ready)
    fun a ⟨hpa,h24,hfields,hret⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hws (keep_zpair hp hr)
  have hznew : ∀j<2,SignedPl a (yBase p+(r+j)) (Zv p σ (p.ℓ*t) (r+j)) (-(q:Int)+1) ((q:Int)-1) := by
    intro j hj
    have hv := hfields j hj
    rw [hsum j hj,paired_pS_addr] at hv
    change SignedPolyIs a.mem (pa a (pS (yBase p+(r+j)))) _ _ _
    rw [hpa.pa (by simp)]
    simpa only [Nat.add_assoc] using hv
  simp only [zfam,Bool.and_eq_true] at hz
  have zold := h.z.keep h.b.l.st.lay hpa hz.1.1.2
  have zall : SignedFam a (yBase p) (r+2) (Zv p σ (p.ℓ*t)) (-(q:Int)+1) ((q:Int)-1) := by
    have h0 := hznew 0 (by decide)
    have h1 := hznew 1 (by decide)
    simpa only [Nat.add_zero,Nat.add_assoc] using (zold.snoc (by simpa only [Nat.add_zero] using h0)).snoc h1
  have yshift : Fam s (yBase p+(r+2)) (p.ℓ-(r+2)) (fun j => Yv p σ (p.ℓ*t) (r+2+j)) := by
    simpa only [show r+1+1=r+2 by omega] using ((h.y.shift (by omega)).shift (by omega))
  have ytail := yshift.keep h.b.l.st.lay hpa hys
  have ha : PositiveIZb p S σ t (r+2) a :=
    ⟨h.b.step hpa hsa hz.1.1.1 hws,zall,ytail,
      h.w.keep h.b.l.st.lay hpa hz.1.2,(h.b.l.st.lay.keepW hpa hz.2).trans h.ones⟩
  have ret : (a.gpr .x0).setWidth 32=if normRq ((List.range 2).map fun j => Zv p σ (p.ℓ*t) (r+j))<p.γ₁-p.β then 1 else 0 := by
    have heq : ((List.range 2).map fun j =>
        add (polyAt s.mem (pairPolyPtr (pa s (yP p r)) j)) (pairedProduct s.mem (pa s cP) (pa s (s1P p r)) j))
        = (List.range 2).map (fun j => Zv p σ (p.ℓ*t) (r+j)) := by
      apply List.map_congr_left
      intro j hj
      exact hsum j (List.mem_range.mp hj)
    rw [heq] at hret
    exact hret
  refine WP.mono_syms (and24_ok a) fun u ⟨hku,hfu⟩ hsu => ?_
  have hpu : PPostB S a u [] := postB24 hku []
  refine ⟨⟨ha.step hpu hsu he hye (by simp),?_⟩,ra.step_layout ha.b.l.st.lay hpu hsu (by simp) (keep_nil hp)⟩
  rw [hfu,bit_and (h24.trans hflag) ret]
  apply bit_congr
  rw [pairedZ_norm (by omega : 0<p.γ₁-p.β)]
  exact pairedZ_prefix

end VG.Proof.MlDsa.AArch64.Sign.CachedChecks

end

/-! ## From `CachedChecksZVector.lean` -/

section

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

end
