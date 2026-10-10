import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming

/-! ## From `OptimizedPairedZVector.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (sc)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedZ_rooted_ok {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r<p.ℓ) (roots : PairedRoots S s) (h : PositiveIZ p S σ t r s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) s (fun u => PositiveIZ p S σ t (r+1) u ∧ PairedRoots S u) := by
  have hc := optimizedZChk_ok hp r hr
  simp only [optimizedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyr,hcr⟩,hyw⟩,hsep⟩,hb⟩,zp⟩,yp⟩,zz⟩,yz⟩,ze⟩,ye⟩,hwp⟩ := hc
  obtain ⟨h,hflag⟩ := h
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
  refine WP.seq (WP.mono_syms (responseProduct_ok ⟨h.b.l.st,h.b.l.k.d.roots⟩
    (responseProductChk_z hp r hr) h.b.c (h.b.l.k.d.s1 r hr)) fun a ⟨hpa,h24a,hprod⟩ hsa => ?_)
  have ra := roots.step_layout h.b.l.st.lay hpa hsa hwp
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
    intro w hw; simp only [List.mem_singleton] at hw; subst w; exact hyw)
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
    rb.step_layout hbstate.b.l.st.lay hpc hsc (by simp)⟩
  rw [hflagc,bit_and (h24b.trans (h24a.trans hflag)) hret]
  exact bit_congr forall_lt_succ

theorem optimizedZ_paired_vector_ok {p : Params} {S : Nat} {σ s : State} {t : Nat}
    (hp : Ok3 p) (roots : PairedRoots S s) (h : PositiveIZ p S σ t 0 s) :
    WP isa (Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector p) s fun u =>
      PositiveIZ p S σ t p.ℓ u ∧ PairedRoots S u := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector
  refine WP.seq (WP.mono (seqR_ok (I:=fun j s => PositiveIZ p S σ t (2*j) s ∧ PairedRoots S s)
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

end VG.Proof.MlDsa.AArch64.Sign

end

/-! ## From `OptimizedPairedZTiming.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedZ_ready {p : Params} {S : Nat} {σ s : State} {t r : Nat}
    (hp : Ok3 p) (hr : r+1<p.ℓ) (roots : PairedRoots S s) (h : PositiveIZ p S σ t r s) :
    Paired.PairedZReady cP (s1P p r) (yP p r) t1P (p.γ₁-p.β) s := by
  have checks := pairedZChk_ok hp r (by omega) hr
  simp only [pairedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,hy⟩,hw⟩,hwy⟩,hww⟩,hcy⟩,hcw⟩,hsy⟩,hsw⟩,hyw⟩,hB⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := checks
  apply pairedZReady_layout h.1.b.l.st.lay roots hc hs hy hw hwy hww hcy hcw hsy hsw hyw
  · refine ⟨h.1.b.c.bound,?_⟩
    intro j hj
    rw [paired_pS_addr]
    simpa only [PositiveReduced,Nat.add_assoc] using (h.1.b.l.k.d.s1 (r+j) (by omega)).bound
  · intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using (h.1.y j (by omega)).1
  · exact hB.1
  · exact hB.2

theorem optimizedZ_pair_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.ℓ)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIZ p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) fun _ _=>True := by
  let I := fun tab s => (∃σ,PositiveIZ p S σ t r s) ∧ PairedRoots S s ∧ s.syms "VG_MLDSA_INV_PAIR"=tab
  have ht (tab : Addr) : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.zPair
    refine seqL (I:=I tab) (J:=fun _=>True) ?_ ?_ ?_
    · apply Paired.pairedZAt_tr (S:=S) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
      rintro x y ⟨L,⟨⟨σ,hx⟩,rx,ex⟩,⟨⟨τ,hy⟩,ry,ey⟩⟩
      exact ⟨pairedZ_ready hp hr rx hx,pairedZ_ready hp hr ry hy,
        L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.sp,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,rx,_⟩
      refine WP.mono (Paired.pairedZAt_ok L.s64 (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (pairedZ_ready hp hr rx hx)) fun _ h=>⟨⟨_,h.1.b⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.1.lrel (fun _ _ h=>h.1.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨x.syms "VG_MLDSA_INV_PAIR",L,⟨⟨σ,hx.1⟩,hx.2,rfl⟩,⟨⟨τ,hy.1⟩,hy.2,h.2.symm⟩⟩

theorem optimizedZ_pair_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.ℓ)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIZ p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.zPair p r) (PairedRS p S E (PositiveIZ p S · t (r+2))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedZ_pair_ok hp hr roots h) (optimizedZ_pair_trace hp hr)

theorem optimizedZ_rooted_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.ℓ)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIZ p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) (PairedRS p S E (PositiveIZ p S · t (r+1))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedZ_rooted_ok hp hr roots h)
    (RelCT.mono (optimizedZ_trace hp hr) (fun _ _ h=>h.root) (fun _ _ h=>h))

theorem optimizedZ_paired_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIZ p S · t 0))
      (Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector p) (PairedRS p S E (PositiveIZ p S · t p.ℓ)) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.zPairedVector
  refine RelCT.seq (RelCT.mono (seqR_tr (Q:=fun j=>PairedRS p S E (PositiveIZ p S · t (2*j)))
    (p.ℓ/2) 0 (fun j _ hj=>?_)) (fun _ _ h=>by simpa only [Nat.mul_zero] using h)
    (fun _ _ h=>by simpa only [Nat.zero_add] using h)) ?_
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedZ_pair_tr hp (by omega : 2*j+1<p.ℓ)
  · split
    · rename_i hodd
      have he : 2*(p.ℓ/2)=p.ℓ-1 := by omega
      have hend : p.ℓ-1+1=p.ℓ := by omega
      simpa only [he,hend] using optimizedZ_rooted_tr (E:=E) hp (by omega : p.ℓ-1<p.ℓ)
    · rename_i heven
      have he : 2*(p.ℓ/2)=p.ℓ := by omega
      rw [he]
      exact RelCT.block_nil (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign

end
