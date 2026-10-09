import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedHints
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming

namespace VG.Proof.MlDsa.AArch64.Sign
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.Sign
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.Optimized

theorem optimizedHint_pair_trace {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) fun _ _=>True := by
  let I := fun tab s => (∃σ,PositiveIH p S σ t r s) ∧ PairedRoots S s ∧ s.syms "VG_MLDSA_INV_PAIR"=tab
  have ht (tab : Addr) : RelCT isa (fun x y => LRel S (sgR p) (sgW p) x y ∧ I tab x ∧ I tab y)
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) fun _ _=>True := by
    unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPair
    unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairRow
    refine seqL (I:=I tab) (J:=fun _=>True) ?_ ?_ ?_
    · apply Paired.pairedHintAt_tr (S:=S) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
        (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _)) (ptr_ok (pS_bases _))
      rintro x y ⟨L,⟨⟨σ,hx⟩,rx,ex⟩,⟨⟨τ,hy⟩,ry,ey⟩⟩
      exact ⟨pairedHint_ready hp hr rx hx,pairedHint_ready hp hr ry hy,
        L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.pa (by change Reg.x28∈bases; decide),L.sp,ex.trans ey.symm⟩
    · rintro x _ ⟨⟨σ,hx⟩,rx,_⟩
      exact WP.mono (pairedHintRow_ok hp hr rx hx) fun _ h=>⟨⟨_,h.1⟩,trivial⟩
    · exact lrel_tr (fun _ _ h=>h.1) (by taint_decide)
  apply RelCT.mono (RelCT.exists_ ht) ?_ (fun _ _ h=>h)
  intro x y h
  have L := h.1.1.lrel (fun _ _ h=>h.1.1.b.l.st)
  obtain ⟨σ,τ,_,_,_,_,hx,hy⟩ := h.1.1
  exact ⟨x.syms "VG_MLDSA_INV_PAIR",L,⟨⟨σ,hx.1⟩,hx.2,rfl⟩,⟨⟨τ,hy.1⟩,hy.2,h.2.symm⟩⟩

theorem optimizedHint_pair_tr {p : Params} {S : Nat} (hp : Ok3 p) {t r : Nat} (hr : r+1<p.k)
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t r))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPair p r) (PairedRS p S E (PositiveIH p S · t (r+2))) :=
  liftPairedR (fun _ _ _ h roots=>optimizedHint_pair_ok hp hr roots h) (optimizedHint_pair_trace hp hr)

theorem optimizedHint_paired_vector_tr {p : Params} {S : Nat} (hp : Ok3 p) {t : Nat}
    {E : State → State → Prop} :
    RelCT isa (PairedRS p S E (PositiveIH p S · t 0))
      (Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector p) (PairedRS p S E (PositiveIH p S · t p.k)) := by
  unfold Impl.MlDsa.AArch64.Sign.Optimized.hintPairedVector
  have he : 2*(p.k/2)=p.k := by rcases hp with rfl|rfl|rfl <;> decide
  simpa only [Nat.mul_zero,Nat.zero_add,he] using
    seqR_tr (Q:=fun j=>PairedRS p S E (PositiveIH p S · t (2*j))) (p.k/2) 0
      (fun j _ hj=>by simpa only [Nat.mul_add,Nat.mul_one] using
        optimizedHint_pair_tr (E:=E) hp (by omega : 2*j+1<p.k))

end VG.Proof.MlDsa.AArch64.Sign
