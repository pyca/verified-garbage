module

import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
public import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedZ
public import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCallTiming
public import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseState
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZLayout
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.AArch64.Syms
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.RegionsSub
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.PairedRootsTiming
meta import VerifiedGarbage.Impl.MlDsa.AArch64.Sign.OptimizedPairedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.PairedZCallTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedResponseState
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZTiming
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedPairedZLayout
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZ
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Sign.OptimizedZCheck
meta import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Entry
meta import VerifiedGarbage.Proof.Framework.RelCTAssoc
meta import VerifiedGarbage.Proof.Framework.AArch64.Syms
meta import VerifiedGarbage.Proof.Framework.Offset
meta import VerifiedGarbage.Proof.Framework.RegionsSub
import Mathlib.Tactic.FinCases

/-! ## From `OptimizedPairedZVector.lean` -/

@[expose] public section

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

end VG.Proof.MlDsa.AArch64.Sign

end
