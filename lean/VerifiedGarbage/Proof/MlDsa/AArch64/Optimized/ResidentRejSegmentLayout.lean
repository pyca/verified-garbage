import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejState

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlKem.AArch64
open VG.Proof.MlDsa.Sample

/-- A stream's coefficient output occupies exactly its share of the public output array. -/
theorem poly_sub {v k : Nat} {σ : State} (hk : k<v) :
    Region.Sub (polyR (polyP σ k)) (aR v σ) :=
  Offset.sub_base (aP σ) (by omega)

theorem segment_input_eq {v : Nat} {σ s : State} (he : Env v σ s) (k off : Nat) :
    segmentInput s k off=bufP σ k+BitVec.ofNat 64 off := by
  unfold segmentInput
  rw [he.x19]
  change scr σ+BitVec.ofNat 64 (840+1008*k+off)=
    (scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 off
  rw [Offset.add_add]

theorem segment_output_eq {v : Nat} {σ s : State} (he : Env v σ s) (k : Nat) :
    segmentOutput s k=polyP σ k := by unfold segmentOutput; rw [he.x21]; rfl

theorem segment_count_eq {v : Nat} {σ s : State} (he : Env v σ s) (k : Nat) :
    countAddress s k=countP σ k := by unfold countAddress; rw [he.x19]; rfl

theorem segment_layout {v k off n : Nat} {σ s : State} (hp : Pre v σ) (he : Env v σ s)
    (hk : k<v) (hn : off+3*n≤1008) :
    StreamLayout s (segmentInput s k off) (segmentOutput s k) n := by
  have hk4 : k<4 := by have:=hp.streams; omega
  rw [segment_input_eq he,segment_output_eq he]
  refine ⟨by omega,?_,?_,?_,?_,?_⟩
  · intro j hj
    change InRegions (s.rd++s.wr)
      (((scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 off)+BitVec.ofNat 64 (3*j)) 16
    rw [Offset.add_add,Offset.add_add]
    exact in_scr_rd hp he.wr (by omega)
  · intro j hj
    change InRegions (s.rd++s.wr)
      (((scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 off)+BitVec.ofNat 64 (3*j)) 4
    rw [Offset.add_add,Offset.add_add]
    exact in_scr_rd hp he.wr (by omega)
  · intro i hi
    rw [he.wr,hp.wr]
    refine ⟨aR v σ,by simp,?_⟩
    change (aR v σ).Contains ((aP σ+BitVec.ofNat 64 (1024*k))+BitVec.ofNat 64 (4*i)) 4
    rw [Offset.add_add]
    exact Offset.contains_base (aP σ) (by omega) (by have:=hp.streams; omega)
  · intro i hi
    rw [he.wr,hp.wr]
    refine ⟨aR v σ,by simp,?_⟩
    change (aR v σ).Contains ((aP σ+BitVec.ofNat 64 (1024*k))+BitVec.ofNat 64 (4*i)) 16
    rw [Offset.add_add]
    exact Offset.contains_base (aP σ) (by omega) (by have:=hp.streams; omega)
  · apply (hp.a_scr.sub_left (poly_sub hk)).symm.sub_left
    change Region.Sub ⟨(scr σ+BitVec.ofNat 64 (840+1008*k))+BitVec.ofNat 64 off,3*n+4⟩ (scrR σ)
    rw [Offset.add_add]
    exact Offset.sub_base (scr σ) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
