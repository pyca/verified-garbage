import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailTiming
import VerifiedGarbage.Proof.MlDsa.AArch64.Optimized.ResidentRejTailBuffers

namespace VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
open VG VG.AArch64
open VG.Impl.MlDsa.AArch64.Optimized.ResidentRej

 def tailChecks (k : Nat) (hk : k<4) : TailChecks k := by
  by_cases h0 : k=0
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h1 : k=1
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  by_cases h2 : k=2
  · subst k; exact ⟨_,_,by taint_decide,by taint_decide⟩
  have h3 : k=3 := by omega
  subst k
  exact ⟨_,_,by taint_decide,by taint_decide⟩

private theorem tail_candidate_eq {v k : Nat} {σ τ s t : State}
    (pub : Pub v σ τ) (hs : TailReady v σ s) (ht : TailReady v τ t) (hk : k<v) :
    candidate s.mem (s.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005))=
      candidate t.mem (t.gpr .x19+BitVec.ofNat 64 (840+1008*k+1005)) := by
  rw [hs.1.env.x19,ht.1.env.x19]
  rw [←Offset.add_add (scr σ) (840+1008*k) 1005,
    ←Offset.add_add (scr τ) (840+1008*k) 1005]
  change candidate s.mem (bufP σ k+BitVec.ofNat 64 1005)=
    candidate t.mem (bufP τ k+BitVec.ofNat 64 1005)
  unfold candidate
  have hb (j : Nat) (hj : j<1008) :
      s.mem (bufP σ k+BitVec.ofNat 64 j)=t.mem (bufP τ k+BitVec.ofNat 64 j) := by
    rw [hs.2 k hk j hj,ht.2 k hk j hj,pub.byte hk j]
  rw [hb 1005 (by decide)]
  have h1 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+1=p+BitVec.ofNat 64 1006 := by
    intro p; exact Offset.add_add p 1005 1
  have h2 : ∀p : Addr,(p+BitVec.ofNat 64 1005)+2=p+BitVec.ofNat 64 1007 := by
    intro p; exact Offset.add_add p 1005 2
  rw [h1,h1,h2,h2,hb 1006 (by decide),hb 1007 (by decide)]

theorem zeroTail_relCT {v k : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ) (hk : k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  have h4 : k<4 := by have:=hp.streams; omega
  have ct : RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t) (Four.zeroTail k)
      (fun _ _ => True) := by
    intro s t tr ur s' t' h es et
    have hs := h.1.1.env
    have ht := h.2.1.env
    exact zeroTailRaw_relCT h4 (h.1.1.length k hk) (tailChecks k h4)
      (hs.sp.trans (pub.2.2.2.1.trans ht.sp.symm))
      (by rw [hs.x19,ht.x19,pub.2.2.1]) (by rw [hs.x21,ht.x21,pub.2.1])
      (by rw [segment_count_eq hs]; exact in_scr_rd hp hs.wr (by unfold counts; omega))
      (by rw [segment_count_eq ht]; exact in_scr_rd hq ht.wr (by unfold counts; omega))
      (by rw [segment_count_eq hs]; exact h.1.1.counts k hk)
      (by rw [segment_count_eq ht,pub.prefix hk 1008]; exact h.2.1.counts k hk)
      (by rw [hs.x19]; exact in_scr_rd hp hs.wr (by omega))
      (by rw [ht.x19]; exact in_scr_rd hq ht.wr (by omega))
      (tail_candidate_eq pub h.1 h.2 hk) _ _ _ _ _ _ ⟨rfl,rfl⟩ es et
  exact (ct.wp (fun _ _ h => ⟨zeroTail_ready hp h.1 hk,zeroTail_ready hq h.2 hk⟩)).mono
    (fun _ _ h => h) (fun _ _ h => h.2)

theorem tailRows_relCT {v : Nat} {σ τ : State}
    (hp : Pre v σ) (hq : Pre v τ) (pub : Pub v σ τ)
    (ks : List Nat) (hks : ∀k∈ks,k<v) :
    RelCT isa (fun s t => TailReady v σ s ∧ TailReady v τ t)
      (ks.foldr (fun k rest => .seq (Four.zeroTail k) rest) (.block []))
      (fun s t => TailReady v σ s ∧ TailReady v τ t) := by
  induction ks with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons k ks ih =>
    exact RelCT.seq (zeroTail_relCT hp hq pub (hks k (by simp)))
      (ih (fun j hj => hks j (by simp [hj])))

end VG.Proof.MlDsa.AArch64.Optimized.ResidentRej
