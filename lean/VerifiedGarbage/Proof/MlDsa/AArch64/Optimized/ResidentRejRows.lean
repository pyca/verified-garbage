import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejFirstBlocks
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentBytes
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejSegmentLayout

/-! ## From `ResidentRejFirstBytes.lean` -/

section

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Proof.MlDsa.AArch64.Sample.Rej4 (F F_block)
open VG.Proof.MlDsa.AArch64.Optimized.Resident (StreamOutput)

theorem firstStream_byte {σ s : State} {k : Nat}
    (h : StreamOutput s.mem (bufP σ k) 10 5 (A0 σ k)) {j : Nat} (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j := by
  have hb := (h (j/168) (by omega)).byte (j := j%168) (by omega)
  change s.mem ((bufP σ k+BitVec.ofNat 64 (168*(j/168)))+BitVec.ofNat 64 (j%168)) = _ at hb
  rw [Offset.add_add,Nat.div_add_mod] at hb
  rw [hb,Resident.permuted_eq_iterF]
  exact (F_block σ k (by omega : j/168<6) (by omega : j%168<168)).symm.trans
    (congrArg (F σ k) (Nat.div_add_mod j 168))

theorem FirstBlocks.byte {v : Nat} {σ s : State} (h : FirstBlocks v σ s)
    {k j : Nat} (hk : k<v) (hj : j<840) :
    s.mem (bufP σ k+BitVec.ofNat 64 j)=F σ k j :=
  firstStream_byte (h.bytes k hk) hj

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej

end

/-! ## From `ResidentRejSegmentEnv.lean` -/

section

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

end

/-! ## From `ResidentRejSegmentFrame.lean` -/

section

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

end

/-! ## From `ResidentRejRows.lean` -/

section

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

end
