import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedVectors
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedPiece
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedRowTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Verify.OptimizedFinish

namespace VG.Proof.MlDsa.AArch64.Verify.Optimized
open VG VG.AArch64 VG.Spec.MlDsa
open VG.Impl.MlDsa.AArch64.KeyGen VG.Impl.MlDsa.AArch64.Verify
open VG.Impl.MlDsa.AArch64.Call (seqR)
open VG.Proof.MlDsa.AArch64.KeyGen
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem compute_piece {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : VFacts p) :
    Piece p S (fun σ s=>VB p σ s ∧ Sign.StaticRoots S s) (VFin p)
      (Impl.MlDsa.AArch64.Verify.Optimized.computeWith keccak.callee P p) := by
  unfold Impl.MlDsa.AArch64.Verify.Optimized.computeWith
  refine Piece.seq (J:=SCx p S p.ℓ false 0) ?_ (Piece.seq (J:=SCx p S p.ℓ true 0) ?_
    (Piece.seq (J:=SCx p S p.ℓ true p.k) ?_ (Piece.of_vpiece (finish_vpiece hP.s16 hP.s64 hF))))
  · refine ⟨fun σ s hp hs=>nttZ_vector_ok hF hp (vb_sc hs.1 hs.2),?_⟩
    exact (nttZ_vector_tr hF).mono
      (fun _ _ ⟨⟨σ,τ,hσ,hτ,pub,ix,iy⟩,et⟩=>⟨⟨σ,τ,hσ,hτ,pub,vb_sc ix.1 ix.2,vb_sc iy.1 iy.2⟩,et⟩)
      (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp ⟨h,A,c,q,hs⟩=>WP.mono (nttC_ok hF hp hs) fun t ht=>⟨h,A,c,q,ht⟩,?_⟩
    exact (nttC_tr hF).mono (fun _ _ h=>h) (fun _ _ _=>trivial)
  · refine ⟨fun σ s hp hs=>rows_ok hP hF hp hs,?_⟩
    have ht := seqR_tr (Q:=fun r=>RootPair p S (SCx p S p.ℓ true r)) p.k 0
      fun r _ hr=>row_tr hP hF (by omega)
    exact ht.mono (fun _ _ h=>h) (fun _ _ _=>trivial)

end VG.Proof.MlDsa.AArch64.Verify.Optimized
