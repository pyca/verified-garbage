import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejStart
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSqueeze

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon

/-- Exact writes of one resident five-block pair, excluding other streams and counts. -/
def fiveWrites (σ : State) (p : Nat) : List Region :=
  [⟨bufP σ (2*p),840⟩,⟨bufP σ (2*p+1),840⟩,pairR (stateP σ p)]

theorem fiveWrites_low {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈fiveWrites σ p,Region.Sub r (lowR σ) := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega)
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega)
  · exact Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oSave
      omega)

theorem fiveWrites_count {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈fiveWrites σ p,(countR σ).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 840+1008*(2*p))
      (n := 32) (k := 840) (by omega) (by decide) (by omega)
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 840+1008*(2*p+1))
      (n := 32) (k := 840) (by omega) (by decide) (by omega)
  · exact (pair_count_disjoint σ hp).symm

theorem fiveWrites_other {σ : State} {p q : Nat} (hp : p<2) (hq : q<2) (hne : p≠q) :
    ∀r∈fiveWrites σ p,(pairR (stateP σ q)).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 840+1008*(2*p))
      (n := 400) (k := 840) (by omega) (by omega) (by omega)
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 840+1008*(2*p+1))
      (n := 400) (k := 840) (by omega) (by omega) (by omega)
  · exact Offset.disjoint (scr σ) (d := 400*q) (e := 400*p)
      (n := 400) (k := 400) (by omega) (by omega) (by omega)

theorem fiveWrites_buffer {σ : State} {p k : Nat} (hp : p<2) (hk : k<4)
    (h0 : k≠2*p) (h1 : k≠2*p+1) :
    ∀r∈fiveWrites σ p,(Region.mk (bufP σ k) 840).Disjoint r := by
  intro r hr
  simp only [fiveWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 840+1008*(2*p))
      (n := 840) (k := 840) (by omega) (by omega) (by omega)
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 840+1008*(2*p+1))
      (n := 840) (k := 840) (by omega) (by omega) (by omega)
  · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 400*p)
      (n := 840) (k := 400) (by omega) (by omega) (by omega)

theorem five_pair_keep {σ : State} {p q : Nat} {s t : State} {A B : Spec.Sha3.State}
    (hp : p<2) (hq : q<2) (hne : p≠q) (hf : Frame (fiveWrites σ p) s.mem t.mem)
    (hpair : PairAt s.mem (stateP σ q) A B) : PairAt t.mem (stateP σ q) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ q) hi) (fiveWrites_other hp hq hne) (by decide)]
  exact hpair i hi

theorem five_count_keep {σ : State} {p k : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hf : Frame (fiveWrites σ p) s.mem t.mem) :
    t.mem.readW (countP σ k) 64=s.mem.readW (countP σ k) 64 := by
  apply hf.readW
  · exact Offset.contains (scr σ) (d := 7904+8*k) (e := 7904) (n := 8) (k := 32)
      (by omega) (by omega) (by decide)
  · exact fiveWrites_count hp
  · decide

theorem five_stream_keep {σ : State} {p k : Nat} {s t : State} {A : Spec.Sha3.State}
    (hp : p<2) (hk : k<4) (h0 : k≠2*p) (h1 : k≠2*p+1)
    (hf : Frame (fiveWrites σ p) s.mem t.mem)
    (hs : Resident.StreamOutput s.mem (bufP σ k) 10 5 A) :
    Resident.StreamOutput t.mem (bufP σ k) 10 5 A := by
  intro i hi
  refine (hs i hi).keep (by decide) hf ?_
  intro r hr
  exact (fiveWrites_buffer hp hk h0 h1 r hr).sub_left (Offset.sub_base (bufP σ k) (by omega))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
