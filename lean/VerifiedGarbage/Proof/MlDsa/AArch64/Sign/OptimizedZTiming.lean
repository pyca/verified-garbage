import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedCommitmentTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

private theorem inB_bases {p : Params} {a : Ptr} {n : Nat} (h : inB (sgB p) a n=true) :
    a.1∈bases := by
  obtain ⟨len,hm,_⟩ := inB_spec h
  exact sgB_bases p (a.1,len) hm

private theorem inB_argOk {p : Params} {a : Ptr} {n : Nat} (h : inB (sgB p) a n=true) :
    (VG.Impl.MlDsa.AArch64.Call.Arg.ptr a).Ok :=
  ptr_ok (bases_kept _ (inB_bases h))

theorem responseProduct_ready {p : Params} {S : Nat} {σ s : State} {out secret : Ptr}
    (hs : RootedSt p S σ s) (hc : responseProductChk p out secret=true)
    (hf : PositiveReduced s.mem (pa s cP)) (hg : PositiveReduced s.mem (pa s secret)) :
    Inverse.ProductCallReady out cP secret (sc oPS) s := by
  simp only [responseProductChk,Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho,ha⟩,hb⟩,hsc⟩,hwo⟩,hws⟩,hoa⟩,hob⟩,hos⟩,has⟩,hbs⟩ := hc
  refine productReady_layout hs.1.lay ho ha hb hsc hwo hws hoa hob hos has hbs
    hs.2.inverse.held hs.2.inverse.fit ?_ hs.2.inverse.readable hf hg
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hwo)
  · exact hs.2.inverse.apart_write (hs.1.lay.inW hws)

theorem responseProduct_tr {p : Params} {S : Nat} {out secret : Ptr}
    (hc : responseProductChk p out secret=true) {Q : State → State → Prop}
    (hQ : ∀x y,Q x y → LRel S (sgR p) (sgW p) x y ∧
      (∃σ,RootedSt p S σ x) ∧ (∃τ,RootedSt p S τ y) ∧
      PositiveReduced x.mem (pa x cP) ∧ PositiveReduced x.mem (pa x secret) ∧
      PositiveReduced y.mem (pa y cP) ∧ PositiveReduced y.mem (pa y secret) ∧
      x.syms "VG_MLDSA_INV_FOLDED"=y.syms "VG_MLDSA_INV_FOLDED") :
    RelCT isa Q (Impl.MlDsa.AArch64.Sign.Optimized.responseProduct out secret) fun _ _=>True := by
  have hc' := hc
  simp only [responseProductChk,Bool.and_eq_true] at hc'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨ho,ha⟩,hb⟩,hsc⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩,_⟩ := hc'
  apply Inverse.productAt_tr (S := S) (inB_argOk ho) (inB_argOk ha)
    (inB_argOk hb) (inB_argOk hsc)
  intro x y h
  obtain ⟨L,⟨σ,hx⟩,⟨τ,hy⟩,fx,gx,fy,gy,et⟩ := hQ x y h
  exact ⟨responseProduct_ready hx hc fx gx,responseProduct_ready hy hc fy gy,
    L.pa (inB_bases ho),L.pa (inB_bases ha),L.pa (inB_bases hb),L.pa (inB_bases hsc),L.sp,et⟩

/-- Trace equality uses only public layout and artifact addresses; all z checks
run before the signer can branch on the accumulated rejection result. -/
theorem optimizedZ_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.ℓ)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIZ p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) fun _ _=>True := by
  have hc := optimizedZChk_ok hp r hr
  simp only [optimizedZChk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyr,hcr⟩,hyw⟩,hsep⟩,hb⟩,zp⟩,yp⟩,_⟩,_⟩,_⟩,_⟩,hwp⟩ := hc
  let I := fun tab s => (∃σ,PositiveIZ p S σ t r s) ∧ s.syms "VG_MLDSA_INV_FOLDED"=tab
  let J := fun s => (∃σ,PositiveIZb p S σ t r s) ∧ RawReduced s.mem (pa s t1P)
  have ht (tab : Addr) : RelCT isa (fun x y=>LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.zR
    refine seqL (I := I tab) (J := J) ?_ ?_ (seqL (J := fun _=>True) ?_ ?_ ?_)
    · apply responseProduct_tr (responseProductChk_z hp r hr)
      intro x y ⟨L,⟨⟨σ,hx⟩,ex⟩,⟨⟨τ,hy⟩,ey⟩⟩
      exact ⟨L,⟨σ,hx.1.b.l.st,hx.1.b.l.k.d.roots⟩,⟨τ,hy.1.b.l.st,hy.1.b.l.k.d.roots⟩,
        hx.1.b.c.bound,(hx.1.b.l.k.d.s1 r hr).bound,
        hy.1.b.c.bound,(hy.1.b.l.k.d.s1 r hr).bound,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,_⟩
      refine WP.mono_syms (responseProduct_ok ⟨hx.1.b.l.st,hx.1.b.l.k.d.roots⟩
        (responseProductChk_z hp r hr) hx.1.b.c (hx.1.b.l.k.d.s1 r hr)) fun a ⟨hpa,_,hprod⟩ hsa => ?_
      refine ⟨⟨_,hpa⟩,⟨σ,hx.1.step hpa hsa zp yp hwp⟩,?_⟩
      rw [hpa.pa (by decide)]
      exact hprod.1
    · apply Response.addNormAt_tr (S := S) (inB_argOk hyr) (inB_argOk hcr)
      intro x y ⟨L,⟨⟨σ,hx⟩,rx⟩,⟨⟨τ,hy⟩,ry⟩⟩
      have fx : Reduced x.mem (pa x (yP p r)) := by
        have h := (hx.y 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      have fy : Reduced y.mem (pa y (yP p r)) := by
        have h := (hy.y 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact ⟨addNormReady_layout L.lx hyr hcr hyw hsep fx rx hb.1 hb.2,
        addNormReady_layout L.ly hyr hcr hyw hsep fy ry hb.1 hb.2,
        L.pa (inB_bases hyr),L.pa (inB_bases hcr),L.sp⟩
    · rintro x L ⟨⟨σ,hx⟩,rx⟩
      have fx : Reduced x.mem (pa x (yP p r)) := by
        have h := (hx.y 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact WP.mono (addNormAt_layout L hyr hcr (addNormReady_layout L hyr hcr hyw hsep fx rx hb.1 hb.2))
        fun _ h=>⟨⟨_,h.1⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.lrel (fun _ _ h=>h.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
  exact ⟨x.syms "VG_MLDSA_INV_FOLDED",L,⟨⟨σ,hx⟩,rfl⟩,⟨⟨τ,hy⟩,h.2.2.symm⟩⟩

theorem optimizedZ_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.ℓ)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIZ p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.zR p r) (RootRS p S E (PositiveIZ p S · t (r+1))) :=
  liftRootR (fun _ _ _ h=>optimizedZ_ok hp hr h) (optimizedZ_trace hp hr)

theorem optimizedZ_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIZ p S · t 0))
      (seqR (Impl.MlDsa.AArch64.Sign.Optimized.zR p) 0 p.ℓ)
      (RootRS p S E (PositiveIZ p S · t p.ℓ)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q := fun r=>RootRS p S E (PositiveIZ p S · t r)) p.ℓ 0
    (fun r _ hr=>optimizedZ_tr hp (by omega))

end VG.Proof.MlDsa.AArch64.Sign
