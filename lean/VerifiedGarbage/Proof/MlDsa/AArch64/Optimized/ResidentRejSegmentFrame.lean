import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentEnv

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

theorem segmentWrites_scratch {v k : Nat} {σ : State} {r : Region}
    (hp : Pre v σ) (hk : k<v) (hr : Region.Sub r (scrR σ))
    (hc : r.Disjoint ⟨countP σ k,8⟩) :
    ∀w∈segmentWrites σ k,r.Disjoint w := by
  intro w hw
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact ((hp.a_scr.sub_left (poly_sub hk)).symm).sub_left hr
  · exact hc

theorem segmentWrites_other_poly {v k j : Nat} {σ : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k) :
    ∀w∈segmentWrites σ k,(polyR (polyP σ j)).Disjoint w := by
  intro w hw
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl
  · exact Offset.disjoint (aP σ) (d := 1024*j) (e := 1024*k) (n := 1024) (k := 1024)
      (by omega) (by have:=hp.streams; omega) (by have:=hp.streams; omega)
  · exact (hp.a_scr.sub_left (poly_sub hj)).sub_right
      (Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega))

theorem segment_count_keep {v k j : Nat} {σ s t : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) :
    t.mem.readW (countP σ j) 64=s.mem.readW (countP σ j) 64 := by
  apply hf.readW (r := ⟨countP σ j,8⟩) (Region.contains_self _ _) _ (by decide)
  apply segmentWrites_scratch hp hk
  · exact Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; have:=hp.streams; omega)
  · exact Offset.disjoint (scr σ) (d := 7904+8*j) (e := 7904+8*k) (n := 8) (k := 8)
      (by omega) (by have:=hp.streams; omega) (by have:=hp.streams; omega)

theorem segment_stored_keep {v k j : Nat} {σ s t : State} {L : List Zq}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hne : j≠k)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) (hL : L.length≤256)
    (hs : Stored s.mem (polyP σ j) L) : Stored t.mem (polyP σ j) L :=
  stored_frame hf (segmentWrites_other_poly hp hk hj hne) hs hL

theorem segment_buffer_keep {v k j d : Nat} {σ s t : State}
    (hp : Pre v σ) (hk : k<v) (hj : j<v) (hd : d<1008)
    (hf : Frame (segmentWrites σ k) s.mem t.mem) :
    t.mem (bufP σ j+BitVec.ofNat 64 d)=s.mem (bufP σ j+BitVec.ofNat 64 d) := by
  apply hf
  intro r hr
  apply (segmentWrites_scratch hp hk (r := ⟨bufP σ j,1008⟩)
    (Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Sample.Rej4.oBuf; have:=hp.streams; omega))
    (Offset.disjoint (scr σ) (d := 840+1008*j) (e := 7904+8*k) (n := 1008) (k := 8)
      (by have:=hp.streams; omega) (by have:=hp.streams; omega) (by have:=hp.streams; omega)) r hr)
  exact Offset.contains_base (bufP σ j) (by omega) (by omega)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
