import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.Sample
open VG.Spec.MlDsa (Zq)

def segmentWrites (σ : State) (k : Nat) : List Region :=
  [polyR (polyP σ k),⟨countP σ k,8⟩]

theorem segmentWrites_sub {v k : Nat} {σ : State} (hk : k<v) (hv : v≤4) :
    ∀r∈segmentWrites σ k,∃R∈[aR v σ,scrR σ],Region.Sub r R := by
  intro r hr
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨aR v σ,by simp,poly_sub hk⟩
  · exact ⟨scrR σ,by simp,Offset.sub_base (scr σ) (by
      unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)⟩

theorem segmentWrites_save {v k : Nat} {σ : State} (hp : Pre v σ) (hk : k<v) :
    ∀r∈segmentWrites σ k,(saveR σ).Disjoint r := by
  intro r hr
  simp only [segmentWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl
  · exact ((hp.a_scr.sub_left (poly_sub hk)).symm).sub_left
      (Offset.sub_base (scr σ) (by decide))
  · exact Offset.disjoint (scr σ) (d := 7968) (e := 7904+8*k) (n := 144) (k := 8)
      (by have:=hp.streams; omega) (by decide) (by have:=hp.streams; omega)

theorem segmentEnv_ok {streams k off n : Nat} {σ s : State} {L : List Zq}
    (hp : Pre streams σ) (he : Env streams σ s) (hk : k<streams)
    (hn : off+3*n≤1008) (hmod : n%4=0) (hL : L.length≤256)
    (hc : (s.mem.readW (countP σ k) 64).toNat=256-L.length)
    (hs : Stored s.mem (polyP σ k) L) (variant : Nat) :
    WP isa (Impl.MlDsa.AArch64.Optimized.ResidentRej.segment variant k off n) s fun t =>
      Env streams σ t ∧ Frame (segmentWrites σ k) s.mem t.mem ∧
      (t.mem.readW (countP σ k) 64).toNat=256-(segmentResult s k off n L).length ∧
      Stored t.mem (polyP σ k) (segmentResult s k off n L) := by
  have hk4 : k<4 := by have:=hp.streams; omega
  have hcount : InRegions s.wr (countP σ k) 8 :=
    in_scr hp he.wr (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega)
  have hread : InRegions (s.rd++s.wr) (countP σ k) 8 := by
    obtain ⟨r,hr,hc⟩ := hcount
    exact ⟨r,List.mem_append.mpr (Or.inr hr),hc⟩
  refine WP.mono (segment_ok variant k off n hk4 (by omega) (by omega) hL hmod
    (segment_layout hp he hk hn) (by rw [segment_count_eq he]; exact hread)
    (by rw [segment_count_eq he]; exact hcount) (by rw [segment_count_eq he]; exact hc)
    (by rw [segment_output_eq he]; exact hs) (by
      rw [segment_output_eq he,segment_count_eq he]
      exact (hp.a_scr.sub_left (poly_sub hk)).sub_right
        (Offset.sub_base (scr σ) (by unfold Impl.MlDsa.AArch64.Optimized.ResidentRej.counts; omega))))
    fun t ⟨ht,hf,hc,hs⟩ => ?_
  rw [segment_output_eq he,segment_count_eq he] at hf
  rw [segment_count_eq he] at hc
  rw [segment_output_eq he] at hs
  refine ⟨he.frameStep hf (segmentWrites_sub hk (by have:=hp.streams; omega))
    (segmentWrites_save hp hk) ht.rd ht.wr ht.sp ?_,hf,hc,hs⟩
  intro r hr
  exact ht.get r (by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
