import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZVector
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming

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
