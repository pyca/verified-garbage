import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedR0Vector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedR0Timing

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (Ptr sc seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem pairedR0_ready {p : Params} {S : Nat} {σ s : State} {t i : Nat}
    (hp : Ok3 p) (hi : i+1<p.k) (roots : PairedRoots S s) (h : PositiveIR p S σ t i s) :
    Paired.PairedLowReady cP (s2P p i) (wP p i) (hP i) t1P p.γ₂ (p.γ₂-p.β) s := by
  have checks := pairedR0Chk_ok hp i (by omega) hi
  simp only [pairedR0Chk,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true] at checks
  obtain ⟨⟨⟨⟨⟨⟨cl,hgb⟩,rr⟩,wr⟩,re⟩,we⟩,hws⟩ := checks
  simp only [pairedLowChk,Bool.and_eq_true] at cl
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc,hs⟩,ho⟩,hl⟩,hw⟩,hwo⟩,hwl⟩,hww⟩,hco⟩,hcl⟩,hcw⟩,hso⟩,hsl⟩,hsw⟩,hol⟩,how⟩,hlw⟩,_⟩ := cl
  obtain ⟨h,_⟩ := h
  have hdata : ∀j<2,PolyIs s.mem (pairPolyPtr (pa s (wP p i)) j) (Wv p σ (p.ℓ*t) (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.w j (by omega)
  have hsecret : ∀j<2,PosPolyIs s.mem (pairPolyPtr (pa s (s2P p i)) j) (S2v p σ (i+j)) := by
    intro j hj
    rw [paired_pS_addr]
    simpa only [Nat.add_assoc] using h.b.l.k.d.s2 (i+j) (by omega)
  have hprod : pairedProductsReduced s.mem (pa s cP) (pa s (s2P p i)) :=
    ⟨h.b.c.bound,fun j hj => (hsecret j hj).bound⟩
  have hsep : ∀r∈[⟨pa s (wP p i),2048⟩,⟨pa s (hP i),2048⟩,⟨pa s t1P,2176⟩],
      (⟨s.syms "VG_MLDSA_INV_PAIR",4096⟩:Region).Disjoint r := by
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl
    · exact roots.apart_write (h.b.l.st.lay.inW hwo)
    · exact roots.apart_write (h.b.l.st.lay.inW hwl)
    · exact roots.apart_write (h.b.l.st.lay.inW hww)
  have ready := pairedLowReady_layout h.b.l.st.lay hc hs ho hl hw hwo hwl hww
    hco hcl hcw hso hsl hsw hol how hlw roots.held roots.fit hsep roots.readable
    hprod (fun j hj => (hdata j hj).1) hgb.1 hgb.2.1 hgb.2.2
  exact ready

theorem optimizedR0_pair_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) fun _ _=>True := by
  let I := fun tab s => (∃σ,PositiveIR p S σ t r s) ∧ PairedRoots S s ∧ s.syms "VG_MLDSA_INV_PAIR"=tab
  have ht (tab : Addr) : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.r0Pair
    refine seqL (I:=I tab) (J:=fun _=>True) ?_ ?_ ?_
    · apply Paired.pairedLowAt_tr (S:=S) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
      rintro x y ⟨L,⟨⟨σ,hx⟩,rx,ex⟩,⟨⟨τ,hy⟩,ry,ey⟩⟩
      exact ⟨pairedR0_ready hp hr rx hx,pairedR0_ready hp hr ry hy,
        L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.sp,ex.trans ey.symm⟩
    · rintro x L ⟨⟨σ,hx⟩,rx,_⟩
      refine WP.mono (Paired.pairedLowAt_ok L.s64 (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (pairedR0_ready hp hr rx hx)) fun _ h=>⟨⟨_,h.1.b⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.1.lrel (fun _ _ h=>h.1.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨x.syms "VG_MLDSA_INV_PAIR",L,⟨⟨σ,hx.1⟩,hx.2,rfl⟩,⟨⟨τ,hy.1⟩,hy.2,h.2.symm⟩⟩

theorem optimizedR0_pair_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.r0Pair p r) (PairedRS p S E (PositiveIR p S · t (r+2))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedR0_pair_ok hp hr roots h) (optimizedR0_pair_trace hp hr)

theorem optimizedR0_paired_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIR p S · t 0))
      (Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase p) (PairedRS p S E (PositiveIR p S · t p.k)) := by
  have heven : p.k%2=0 := by rcases hp with rfl|rfl|rfl <;> decide
  unfold Impl.MlDsa.AArch64.Sign.Optimized.pairedLowPhase
  rw [ite_eq_left heven]
  refine RelCT.seq (RelCT.mono (seqR_tr (Q:=fun j=>PairedRS p S E (PositiveIR p S · t (2*j)))
    (p.k/2) 0 (fun j _ hj=>?_)) (fun _ _ h=>by simpa only [Nat.mul_zero] using h)
    (fun _ _ h=>by simpa only [Nat.zero_add] using h)) ?_
  · simpa only [Nat.mul_add,Nat.mul_one] using optimizedR0_pair_tr hp (by omega : 2*j+1<p.k)
  · have he : 2*(p.k/2)=p.k := by omega
    rw [he]
    exact RelCT.block_nil (fun _ _ h=>h)

end VG.Proof.MlDsa.AArch64.Sign
