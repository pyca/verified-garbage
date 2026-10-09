import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejChecks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejEnvTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejAdaptive

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

abbrev PrefixPair (v blocks n : Nat) (σ τ s t : State) :=
  Rows v blocks σ (fun k => prefixRow σ k n) s ∧
  Rows v blocks τ (fun k => prefixRow τ k n) t

theorem prefixFour_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : ∀k<4,SegmentChecks k off n) :
    RelCT isa (PrefixPair 4 blocks off σ τ) (Four.batch 0 off n)
      (PrefixPair 4 blocks (off+3*n) σ τ) := by
  refine (batchFour_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem prefixTwo_relCT {blocks off n : Nat} {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ)
    (hn : off+3*n≤168*blocks) (hmod : n%4=0) (ho : off%3=0)
    (checks : ∀k<2,SegmentChecks k off n) :
    RelCT isa (PrefixPair 2 blocks off σ τ) (Two.batch 0 off n)
      (PrefixPair 2 blocks (off+3*n) σ τ) := by
  refine (batchTwo_relCT (L := fun k => prefixRow σ k off) hp hq pub hn hmod 0 checks).mono ?_ ?_
  · intro s t h
    exact ⟨h.1,h.2.congr (fun k hk => (pub.prefix hk off).symm)⟩
  · intro s t h
    exact ⟨h.1.congr (fun k _ => rowResult_prefix σ k off n ho),
      h.2.congr (fun k hk => (rowResult_prefix σ k off n ho).trans (pub.prefix hk _))⟩

theorem parseFiveFour_relCT {σ τ : State}
    (hp : Pre 4 σ) (hq : Pre 4 τ) (pub : Pub 4 σ τ) :
    RelCT isa (fun s t => FirstBlocks 4 σ s ∧ FirstBlocks 4 τ t)
      (.seq (Four.batch 0 0 168) (Four.batch 0 504 112))
      (PrefixPair 4 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 4 5 504 σ τ)
  · exact (prefixFour_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) firstChecks).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixFour_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) secondChecks

theorem parseFiveTwo_relCT {σ τ : State}
    (hp : Pre 2 σ) (hq : Pre 2 τ) (pub : Pub 2 σ τ) :
    RelCT isa (fun s t => FirstBlocks 2 σ s ∧ FirstBlocks 2 τ t)
      (.seq (Two.batch 0 0 168) (Two.batch 0 504 112))
      (PrefixPair 2 5 840 σ τ) := by
  apply RelCT.seq (R := PrefixPair 2 5 504 σ τ)
  · exact (prefixTwo_relCT hp hq pub (by decide : 0+3*168≤168*5)
      (by decide) (by decide) (fun k hk => firstChecks k (by omega))).mono
      (fun _ _ h => ⟨h.1.rows,h.2.rows⟩) (fun _ _ h => h)
  · exact prefixTwo_relCT hp hq pub (by decide : 504+3*112≤168*5)
      (by decide) (by decide) (fun k hk => secondChecks k (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
