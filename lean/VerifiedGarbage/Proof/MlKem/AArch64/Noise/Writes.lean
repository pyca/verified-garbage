module
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Cover
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Layout
public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Pair

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Offsets
import VerifiedGarbage.Proof.Framework.Offset

/-! # Exact paired-noise footprints and separated retained outputs -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Proof.Sha3.AArch64.Neon

def writes (L : KemLay) (kg : Bool) (B : Addr) (n : Nat) : List Region :=
 pairWrites (B+BitVec.ofNat 64 (scratchOff kg))
   (B+BitVec.ofNat 64 (outOff L kg n)) (B+BitVec.ofNat 64 (outOff L kg (n+1)))
   (B+BitVec.ofNat 64 (nttOff kg))

theorem writes_apart {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n off len : Nat} (hn : n+1<2*L.k) (hfit : off+len≤L.scl)
    (hss : off+len≤scratchOff kg ∨ scratchOff kg+2048≤off)
    (hns : off+len≤nttOff kg ∨ nttOff kg+1024≤off)
    (hf : off+len≤outOff L kg n ∨ outOff L kg n+1024≤off)
    (hg : off+len≤outOff L kg (n+1) ∨ outOff L kg (n+1)+1024≤off) :
    ∀r∈writes L kg B n, (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint r := by
  have lim := layout_limits wf kg
  have f0 := outOff_fits wf room kg (by omega : n<2*L.k)
  have f1 := outOff_fits wf room kg hn
  have sep {o k : Nat} (h : off+len≤o ∨ o+k≤off) (fit : o+k≤L.scl) :=
    Offset.disjoint B h (by omega : off+len≤2^64) (by omega : o+k≤2^64)
  intro r hr
  simp only [writes,pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1800,48⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega) (by omega)
  · exact sep (by omega) (by omega)
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 400,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega) (by omega)
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 528,128⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega) (by omega)
  · change (Region.mk (B+BitVec.ofNat 64 off) len).Disjoint
      ⟨B+BitVec.ofNat 64 (scratchOff kg)+BitVec.ofNat 64 1536,136⟩
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact sep (by omega) (by omega)
  · exact sep hf f0
  · exact sep hg f1
  · exact sep hns lim.2.2.1

theorem writes_seed_far {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n : Nat} (hn : n+1<2*L.k) :
    ∀r∈writes L kg B n, (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint r := by
  have lim := layout_limits wf kg
  have lo0 := outOff_low wf room kg n
  have lo1 := outOff_low wf room kg (n+1)
  change nttOff kg+1024≤_ at lo0 lo1
  exact writes_apart wf room kg B hn (by omega) (Or.inl lim.2.1)
    (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))

theorem writes_old_far {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr)
    {n j : Nat} (hn : n+1<2*L.k) (hj : j<n) :
    ∀r∈writes L kg B n, (polyRegion (B+BitVec.ofNat 64 (outOff L kg j))).Disjoint r := by
  have lim := layout_limits wf kg
  have lo := outOff_low wf room kg j
  change nttOff kg+1024≤_ at lo
  have f := outOff_fits wf room kg (by omega : j<2*L.k)
  exact writes_apart wf room kg B hn f (Or.inr (by omega)) (Or.inr lo)
    (Or.inl (outOff_order wf room kg hj)) (Or.inl (outOff_order wf room kg (by omega)))

end VG.Proof.MlKem.AArch64.Noise
