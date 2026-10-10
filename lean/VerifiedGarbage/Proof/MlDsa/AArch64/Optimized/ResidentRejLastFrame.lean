import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejLastPair
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.Sha3.AArch64.Neon
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

theorem lastWrites_count {σ : State} {p : Nat} (hp : p<2) :
    ∀r∈lastWrites σ p,(countR σ).Disjoint r := by
  intro r hr
  simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact (pair_count_disjoint σ hp).symm
  · rw [lastPtr_eq]
    exact Offset.disjoint (scr σ) (d := 7904) (e := 1680+1008*(2*p))
      (n := 32) (k := 168) (by omega) (by decide) (by omega)
  · rw [lastPtr_eq]
    exact Offset.disjoint (scr σ) (d := 7904) (e := 1680+1008*(2*p+1))
      (n := 32) (k := 168) (by omega) (by decide) (by omega)
  · exact Offset.disjoint (scr σ) (d := 7904) (e := 4880) (n := 32) (k := 136)
      (by decide) (by decide) (by decide)

theorem last_count_keep {σ : State} {p k : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hf : Frame (lastWrites σ p) s.mem t.mem) :
    t.mem.readW (countP σ k) 64=s.mem.readW (countP σ k) 64 := by
  apply hf.readW
  · exact Offset.contains (scr σ) (d := 7904+8*k) (e := 7904) (n := 8) (k := 32)
      (by omega) (by omega) (by decide)
  · exact lastWrites_count hp
  · decide

theorem last_pair_keep {σ : State} {p q : Nat} {s t : State} {A B : Spec.Sha3.State}
    (hp : p<2) (hq : q<2) (hne : p≠q) (hf : Frame (lastWrites σ p) s.mem t.mem)
    (hpair : PairAt s.mem (stateP σ q) A B) : PairAt t.mem (stateP σ q) A B := by
  intro i hi
  rw [hf.read (pair_contains (stateP σ q) hi) (by
    intro r hr
    simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint (scr σ) (d := 400*q) (e := 400*p) (n := 400) (k := 400)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p)) (n := 400) (k := 168)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 400*q) (e := 1680+1008*(2*p+1)) (n := 400) (k := 168)
        (by omega) (by omega) (by omega)
    · exact Offset.disjoint (scr σ) (d := 400*q) (e := 4880) (n := 400) (k := 136)
        (by omega) (by omega) (by decide)) (by decide)]
  exact hpair i hi

theorem last_buffer_keep {σ : State} {p k j n : Nat} {s t : State}
    (hp : p<2) (hk : k<4) (hn : n≤1008) (hj : j<n)
    (h0 : k=2*p → n≤840) (h1 : k=2*p+1 → n≤840)
    (hf : Frame (lastWrites σ p) s.mem t.mem) :
    t.mem (bufP σ k+BitVec.ofNat 64 j)=s.mem (bufP σ k+BitVec.ofNat 64 j) := by
  apply hf
  intro r hr
  have hd : (Region.mk (bufP σ k) n).Disjoint r := by
    simp only [lastWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 400*p) (n := n) (k := 400)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p)) (n := n) (k := 168)
        (by omega) (by omega) (by omega)
    · rw [lastPtr_eq]
      exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 1680+1008*(2*p+1)) (n := n) (k := 168)
        (by omega) (by omega) (by omega)
    · exact Offset.disjoint (scr σ) (d := 840+1008*k) (e := 4880) (n := n) (k := 136)
        (by omega) (by omega) (by decide)
  exact hd _ (Offset.contains_base (bufP σ k) (by omega) (by omega))

theorem last_stored_keep {v p k : Nat} {σ s t : State} {L : List Zq}
    (hp : Pre v σ) (hp2 : p<2) (hk : k<v) (hL : L.length≤256)
    (hf : Frame (lastWrites σ p) s.mem t.mem) (hs : Stored s.mem (polyP σ k) L) :
    Stored t.mem (polyP σ k) L := by
  apply stored_frame hf _ hs hL
  intro r hr
  exact (hp.a_scr.sub_left (poly_sub hk)).sub_right
    (fun x hx => (Region.sub_prefix (by decide : 7968≤8192)) x (lastWrites_low hp2 r hr x hx))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
