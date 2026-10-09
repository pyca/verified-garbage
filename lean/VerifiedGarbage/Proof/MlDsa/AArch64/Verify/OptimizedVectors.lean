import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRow
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedNttTiming

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen

theorem vb_sc {p : Params} {S : Nat} {σ s : State} (h : VB p σ s) (ht : Sign.StaticRoots S s) :
    SCx p S 0 false 0 σ s := by
  obtain ⟨hh,A,c,q,hs⟩:=Verify.vb_sc h
  refine ⟨hh,A,c,q,hs.vc,ht,hs.hh,hs.hint,hs.nok,hs.gd,hs.a,?_,hs.c,hs.rows,hs.x24⟩
  intro i hi
  simpa only [Stored,Nat.not_lt_zero,decide_false,Bool.false_eq_true,↓reduceIte] using hs.z i hi

theorem nttZ_vector_ok {p : Params} (hF : VFacts p) {S : Nat} {σ s : State} (hp : vPre p S σ)
    (hs : SCx p S 0 false 0 σ s) :
    WP isa (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ) s
      (SCx p S p.ℓ false 0 σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun i=>SCx p S i false 0 σ) p.ℓ 0
    (fun i _ hi s ⟨h,A,c,q,hs⟩=>WP.mono (nttZ_ok hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

theorem nttZ_vector_tr {p : Params} (hF : VFacts p) {S : Nat} :
    RelCT isa (RootPair p S (SCx p S 0 false 0))
      (seqR (fun i=>Impl.MlDsa.AArch64.Verify.Optimized.forward (zP p i)) 0 p.ℓ)
      (RootPair p S (SCx p S p.ℓ false 0)) := by
  simpa only [Nat.zero_add] using seqR_tr (Q:=fun i=>RootPair p S (SCx p S i false 0)) p.ℓ 0 fun i _ hi=>nttZ_tr hF (by omega)

theorem rows_ok {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p)
    {σ s : State} (hp : vPre p S σ) (hs : SCx p S p.ℓ true 0 σ s) :
    WP isa (seqR (Impl.MlDsa.AArch64.Verify.Optimized.row P p) 0 p.k) s
      (SCx p S p.ℓ true p.k σ) := by
  simpa only [Nat.zero_add] using seqR_ok (I:=fun r=>SCx p S p.ℓ true r σ) p.k 0
    (fun r _ hr s ⟨h,A,c,q,hs⟩=>WP.mono (row_ok hP hF hp (by omega) hs)
      fun t ht=>⟨h,A,c,q,ht⟩) s hs

end VG.Proof.MlDsa.AArch64.Verify.Optimized
