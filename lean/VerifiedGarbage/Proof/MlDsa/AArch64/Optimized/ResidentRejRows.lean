import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFirstBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentFrame

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F)
open VG.Proof.Sha3.AArch64.Neon (PairAt pairR wordAddr pair_contains)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (permuted)
open VG.Spec.MlDsa (Zq)

/-- Per-stream rejection state after a fixed public number of SHAKE blocks. -/
structure Rows (v blocks : Nat) (σ : State) (L : Nat → List Zq) (s : State) : Prop where
  env : Env v σ s
  blockBound : blocks≤6
  pairs : ∀p,2*p+1<v → PairAt s.mem (stateP σ p)
    (permuted (A0 σ (2*p)) blocks) (permuted (A0 σ (2*p+1)) blocks)
  bytes : ∀k<v,∀j<168*blocks,s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j
  length : ∀k<v,(L k).length≤256
  counts : ∀k<v,(s.mem.readW (countP σ k) 64).toNat=256-(L k).length
  stored : ∀k<v,Stored s.mem (polyP σ k) (L k)

theorem FirstBlocks.rows {v : Nat} {σ s : State} (h : FirstBlocks v σ s) :
    Rows v 5 σ (fun _ => []) s := by
  refine ⟨h.env,by decide,h.pairs,fun k hk j hj => h.byte hk hj,by simp,?_,?_⟩
  · intro k hk
    rw [h.counts k hk]
    rfl
  · intro k hk i hi
    simp at hi

def streamBytes (σ : State) (k off n : Nat) : List Byte :=
  (List.range n).map fun j => F σ k (off+j)

def rowResult (σ : State) (k off n : Nat) (L : List Zq) : List Zq :=
  rnFold L (streamBytes σ k off (3*n))

theorem segmentResult_rows {v blocks k off n : Nat} {σ s : State} {L : Nat → List Zq}
    (h : Rows v blocks σ L s) (hk : k<v) (hn : off+3*n≤168*blocks) :
    segmentResult s k off n (L k)=rowResult σ k off n (L k) := by
  unfold segmentResult rowResult
  congr 1
  rw [segment_input_eq h.env]
  unfold Spec.Sha3.bytesAt streamBytes
  apply List.map_congr_left
  intro j hj
  have hjn : j<3*n := List.mem_range.mp hj
  rw [Offset.add_add]
  exact h.bytes k hk (off+j) (by omega)

theorem segment_pair_keep {v k p : Nat} {σ s t : State} {A B : Spec.Sha3.State}
    (hp : Pre v σ) (hk : k<v) (hpv : 2*p+1<v)
    (hf : Frame (segmentWrites σ k) s.mem t.mem)
    (hs : PairAt s.mem (stateP σ p) A B) : PairAt t.mem (stateP σ p) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ p) hi) (segmentWrites_scratch hp hk
    (Offset.sub_base (scr σ) (by have:=hp.streams; omega))
    (Offset.disjoint (scr σ) (d := 400*p) (e := 7904+8*k) (n := 400) (k := 8)
      (by have:=hp.streams; omega) (by have:=hp.streams; omega) (by have:=hp.streams; omega))) (by decide)]
  exact hs i hi

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
