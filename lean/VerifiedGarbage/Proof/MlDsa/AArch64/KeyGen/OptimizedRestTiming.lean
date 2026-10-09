import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedCorrect
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedRowTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedNttTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.KeyGen.OptimizedPieceTiming

namespace VG.Proof.MlDsa.AArch64.KeyGen.Optimized
open VG VG.AArch64 VG.Impl.MlDsa.AArch64.KeyGen
open VG.Impl.MlDsa.AArch64.Call
open VG.Spec.MlDsa (Params)
variable {keccak : Proof.Sha3.AArch64.Permutation}

theorem canonicalRootPair {p : Params} {S : Nat} {x y : State}
    (h : RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p (p.ℓ+p.k) 0 0) x y) :
    RootPair p S (KRx p (p.ℓ+p.k) 0 0) x y :=
  rootPair_mono (fun _ _ ⟨A,T,R,h⟩ => ⟨A,T,R,PositiveKR.of_canonical h⟩) h

theorem rest_tr_of_rows {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hr : ∀i<p.k,RelCT isa (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i)
      (RootPair p S (KRx p (p.ℓ+p.k) p.ℓ (i+1)))) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) fun _ _ => True := by
  unfold Impl.MlDsa.AArch64.KeyGen.Optimized.restWith
  apply RelCT.seq (piece_rooted (copies_piece hF) (by change 0≤S; omega) hP.s64)
  apply RelCT.seq
    (seqR_tr (Q := fun j => RootPair p S (VG.Proof.MlDsa.AArch64.KeyGen.KRx p j 0 0))
      (p.ℓ+p.k) 0 (fun j _ hj => piece_rooted (packSecret_piece hP hF (by omega)) (hdpack j (by omega)) hP.s64))
  simp only [Nat.zero_add]
  apply RelCT.seq
    (RelCT.mono (seqR_tr (Q := fun j => RootPair p S (KRx p (p.ℓ+p.k) j 0))
      p.ℓ 0 (fun j _ hj => nttSecret_relCT hF (by omega)))
      (fun _ _ h => canonicalRootPair h) (fun _ _ h => h))
  simp only [Nat.zero_add]
  apply RelCT.seq (seqR_tr (Q := fun i => RootPair p S (KRx p (p.ℓ+p.k) p.ℓ i))
    p.k 0 (fun i _ hi => hr i (by omega)))
  simp only [Nat.zero_add]
  apply RelCT.mono (trHash_piece (keccak := keccak) hF hP.s16 hP.s64).tr
  · rintro x y ⟨⟨σ,τ,hσ,hτ,pub,hx,hy⟩,_⟩
    exact ⟨σ,τ,hσ,hτ,pub,hx.1,hy.1⟩
  · intro _ _ _
    trivial

theorem rest_relCT {P : Prims} {S : Nat} (hP : PrimsOk P S) {p : Params} (hF : PFacts p)
    (hdpack : ∀j<p.ℓ+p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.packSecret P p j).aarch64Depth≤S)
    (hdrow : ∀i<p.k,16*(Impl.MlDsa.AArch64.KeyGen.Optimized.row P p i).aarch64Depth≤S) :
    RelCT isa (RootPair p S (KSamp p · (p.k*p.ℓ) (p.ℓ+p.k)))
      (Impl.MlDsa.AArch64.KeyGen.Optimized.restWith keccak.callee P p) (R p S (KFin p)) :=
  rootPair_finish (fun _ _ hp h roots => rest_ok hP hF hp h roots hdpack hdrow)
    (rest_tr_of_rows hP hF hdpack (fun i hi => row_relCT hP hF hi (hdrow i hi)))

end VG.Proof.MlDsa.AArch64.KeyGen.Optimized
