module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Execute a pair using only the public scratch allocation -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon


theorem noisePair_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} {n : Nat} (hn : n+1<2*L.k) (hB : s.gpr .x28=B)
    (hc : Covers [⟨B,L.scl⟩] s.wr) :
    WP isa (Impl.MlKem.AArch64.Noise.noisePair L kg n) s fun t =>
      Kept (pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
        (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (B+BitVec.ofNat 64 (nttOff kg))) s t ∧
      Proof.MlKem.PolyIs t.mem (B+BitVec.ofNat 64 (outOff L kg n))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) n (transformed L kg n)) ∧
      Proof.MlKem.PolyIs t.mem (B+BitVec.ofNat 64 (outOff L kg (n+1)))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) (n+1) (transformed L kg (n+1))) := by
  have lim := layout_limits wf kg
  have fit0 := outOff_fits wf room kg (by omega : n<2*L.k)
  have fit1 := outOff_fits wf room kg hn
  have low0 := outOff_low wf room kg n
  have low1 := outOff_low wf room kg (n+1)
  change nttOff kg+1024≤outOff L kg n at low0
  change nttOff kg+1024≤outOff L kg (n+1) at low1
  have order := outOff_order wf room kg (Nat.lt_succ_self n)
  have size : L.scl<2^64 := by omega
  have iw {o l : Nat} (h : o+l≤L.scl) := inScratch hc h size
  have ir {o l : Nat} (h : o+l≤L.scl) : InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 o) l :=
    by obtain ⟨r,hr,hc⟩ := iw h; exact ⟨r,List.mem_append_right _ hr,hc⟩
  have cw {o l : Nat} (h : o+l≤L.scl) := coversScratch hc h
  have sep {o l d k : Nat} (h : o+l≤d ∨ d+k≤o) (ho : o+l≤L.scl) (hd : d+k≤L.scl) :=
    Offset.disjoint B h (by omega : o+l≤2^64) (by omega : d+k≤2^64)
  have snorm (k : Nat) : B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 k =
      B+BitVec.ofNat 64 (scratchOff kg+k) := by rw [BitVec.add_assoc,← BitVec.ofNat_add]
  refine noisePair_ok kg (by have := wf.facts; omega) (by omega) (by omega)
    (by rw [hB]; rfl) (by rw [hB]; rfl) (by rw [hB]) (by rw [hB]) (by rw [hB]; rfl)
    (fun j hj => ?_) (fun j hj => ?_) (fun j hj => ?_) ?_ ?_ ?_
  · rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact ir (by omega)
  · change InRegions s.wr (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*j)) 16
    rw [snorm]; exact iw (by omega)
  · rw [snorm]; exact iw (by omega)
  · change (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [snorm]; exact sep (Or.inl (by omega)) (by omega) (by omega)
  · exact sep (Or.inl lim.2.1) (by omega) (by omega)
  · constructor
    · intro i hi
      change InRegions (s.rd++s.wr) (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 (16*i)) 16
      rw [snorm]; exact ir (by omega)
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega)
    · intro i hi
      change InRegions s.wr ((B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528)+BitVec.ofNat 64 (8*i)) 8
      rw [snorm,BitVec.add_assoc,← BitVec.ofNat_add]; exact iw (by omega)
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg),400⟩,
        ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩] s.wr
      rw [snorm]; exact coversTwo (cw (by omega)) (cw (by omega))
    · intro i hi; rw [snorm]; exact ir (by omega)
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg n),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega)) (cw fit0))
    · change Covers [⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩,
        ⟨B+BitVec.ofNat 64 (outOff L kg (n+1)),1024⟩] (s.rd++s.wr)
      rw [snorm]; exact covers_rw' (coversTwo (cw (by omega)) (cw fit1))
    · exact coversTwo (cw fit0) (cw lim.2.2.1)
    · exact coversTwo (cw fit1) (cw lim.2.2.1)
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega)) (by omega) fit0
    · change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint _
      rw [snorm]; exact sep (Or.inl (by omega)) (by omega) fit1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528) 128).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl
      · exact sep (Or.inl (by omega)) (by omega) fit0
      · exact sep (Or.inl (by omega)) (by omega) lim.2.2.1
    · exact sep (Or.inl order) fit0 fit1
    · exact sep (Or.inr low0) fit0 lim.2.2.1
    · exact sep (Or.inr low1) fit1 lim.2.2.1
    · intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      change (Region.mk (B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800) 48).Disjoint r
      rw [snorm]
      rcases hr with rfl | rfl | rfl
      · exact sep (Or.inl (by omega)) (by omega) fit0
      · exact sep (Or.inl (by omega)) (by omega) fit1
      · exact sep (Or.inl (by omega)) (by omega) lim.2.2.1

end VG.Proof.MlKem.AArch64.Noise
