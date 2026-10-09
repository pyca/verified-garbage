import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming

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
    (VG.Impl.MlDsa.AArch64.Call.Arg.ptr a).Ok := ptr_ok (bases_kept _ (inB_bases h))

/-- Trace equality uses only public layout and artifact addresses; all r0 checks
run before the signer can branch on the accumulated rejection result. -/
theorem optimizedR0_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.k)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) fun _ _=>True := by
  have hc := optimizedR0Chk_ok hp r hr
  simp only [optimizedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨cl,hgb⟩,rp⟩,wp⟩,_⟩,_⟩,_⟩,_⟩,hwp⟩ := hc
  simp only [subLowNormChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hwr,hcr⟩,hlr⟩,hww⟩,hwl⟩,hwc⟩,hwo⟩,hco⟩,_⟩ := cl
  let I := fun tab s => (∃σ,PositiveIR p S σ t r s) ∧ s.syms "VG_MLDSA_INV_FOLDED"=tab
  let J := fun s => (∃σ,PositiveIRb p S σ t r s) ∧ RawReduced s.mem (pa s t1P)
  have ht (tab : Addr) : RelCT isa (fun x y=>LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.r0R
    refine seqL (I := I tab) (J := J) ?_ ?_ (seqL (J := fun _=>True) ?_ ?_ ?_)
    · apply responseProduct_tr (responseProductChk_r0 hp r hr)
      intro x y ⟨L,⟨⟨σ,hx⟩,ex⟩,⟨⟨τ,hy⟩,ey⟩⟩
      exact ⟨L,⟨σ,hx.1.b.l.st,hx.1.b.l.k.d.roots⟩,⟨τ,hy.1.b.l.st,hy.1.b.l.k.d.roots⟩,
        hx.1.b.c.bound,(hx.1.b.l.k.d.s2 r hr).bound,
        hy.1.b.c.bound,(hy.1.b.l.k.d.s2 r hr).bound,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,_⟩
      refine WP.mono_syms (responseProduct_ok ⟨hx.1.b.l.st,hx.1.b.l.k.d.roots⟩
        (responseProductChk_r0 hp r hr) hx.1.b.c (hx.1.b.l.k.d.s2 r hr)) fun a ⟨hpa,_,hprod⟩ hsa => ?_
      refine ⟨⟨_,hpa⟩,⟨σ,hx.1.step hpa hsa rp wp hwp⟩,?_⟩
      rw [hpa.pa (by decide)]
      exact hprod.1
    · apply Response.subLowNormAt_tr (S := S) (inB_argOk hwr) (inB_argOk hcr) (inB_argOk hlr)
      intro x y ⟨L,⟨⟨σ,hx⟩,rx⟩,⟨⟨τ,hy⟩,ry⟩⟩
      have fx : Reduced x.mem (pa x (wP p r)) := by
        have h := (hx.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      have fy : Reduced y.mem (pa y (wP p r)) := by
        have h := (hy.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact ⟨subLowNormReady_layout L.lx hwr hcr hlr hww hwl hwc hwo hco fx rx hgb.1 hgb.2.1 hgb.2.2,
        subLowNormReady_layout L.ly hwr hcr hlr hww hwl hwc hwo hco fy ry hgb.1 hgb.2.1 hgb.2.2,
        L.pa (inB_bases hwr),L.pa (inB_bases hcr),L.pa (inB_bases hlr),L.sp⟩
    · rintro x L ⟨⟨σ,hx⟩,rx⟩
      have fx : Reduced x.mem (pa x (wP p r)) := by
        have h := (hx.w 0 (by omega)).1
        simpa only [Nat.add_zero] using h
      exact WP.mono (subLowNormAt_layout L hwr hcr hlr
        (subLowNormReady_layout L hwr hcr hlr hww hwl hwc hwo hco fx rx hgb.1 hgb.2.1 hgb.2.2))
        fun _ h=>⟨⟨_,h.1⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.lrel (fun _ _ h=>h.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1
  exact ⟨x.syms "VG_MLDSA_INV_FOLDED",L,⟨⟨σ,hx⟩,rfl⟩,⟨⟨τ,hy⟩,h.2.2.symm⟩⟩

theorem optimizedR0_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r<p.k)
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0R p r) (RootRS p S E (PositiveIR p S · t (r+1))) :=
  liftRootR (fun _ _ _ h=>optimizedR0_ok hp hr h) (optimizedR0_trace hp hr)

theorem optimizedR0_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (RootRS p S E (PositiveIR p S · t 0))
      (seqR (Impl.MlDsa.AArch64.Sign.Optimized.r0R p) 0 p.k)
      (RootRS p S E (PositiveIR p S · t p.k)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q := fun r=>RootRS p S E (PositiveIR p S · t r)) p.k 0
    (fun r _ hr=>optimizedR0_tr hp (by omega))

end VG.Proof.MlDsa.AArch64.Sign
