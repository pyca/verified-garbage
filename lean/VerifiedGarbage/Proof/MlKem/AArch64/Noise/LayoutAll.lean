module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Writes
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutPair
import VerifiedGarbage.Proof.MlKem.AArch64.Noise.All
import VerifiedGarbage.Proof.Framework.Offset

/-! # Complete paired sampling of all secrets and retained errors -/
@[expose] public section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64

def allWrites (L : KemLay) (kg : Bool) (B : Addr) : List Region :=
 (List.range L.k).flatMap fun i => writes L kg B (2*i)

theorem allWrites_seed_far {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool) (B : Addr) :
    ∀r∈allWrites L kg B, (Region.mk (B+BitVec.ofNat 64 (seedOff kg)) 32).Disjoint r := by
  intro r hr
  obtain ⟨i,hi,hr⟩ := List.mem_flatMap.mp hr
  exact writes_seed_far wf room kg B (by have := List.mem_range.mp hi; omega) r hr

theorem noiseAll_layout {s : State} {L : KemLay} (wf : L.Wf) (room : Room L) (kg : Bool)
    {B : Addr} (hB : s.gpr .x28=B) (hc : Covers [⟨B,L.scl⟩] s.wr) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAll L kg) s fun t =>
      Kept (allWrites L kg B) s t ∧
      ∀j<2*L.k, Spec.MlKem.PolyIs t.mem (B+BitVec.ofNat 64 (outOff L kg j))
        (sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j)) := by
  refine all_loop_ok kg (by have := wf.facts; omega) (allWrites L kg B)
    (fun j => B+BitVec.ofNat 64 (outOff L kg j))
    (fun j => sampled s.mem (B+BitVec.ofNat 64 (seedOff kg)) j (transformed L kg j))
    (fun i => writes L kg B (2*i)) ?_ ?_ ?_
  · intro i hi r hr
    exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,hr⟩
  · intro i hi j hj
    exact writes_old_far wf room kg B (by omega) hj
  · intro i hi t kt
    refine WP.mono (noisePair_layout (B := B) wf room kg (by omega : 2*i+1<2*L.k)
      (by rw [kt.cs .x28 (by decide) (by decide)]; exact hB)
      (by rw [kt.wr]; exact hc)) fun u ⟨ku,pu,qu⟩ => ?_
    have he := Proof.MlKem.bytesAt_frame kt.frame (allWrites_seed_far wf room kg B) (by decide)
    exact ⟨ku,by simpa only [sampled,he] using pu,by simpa only [sampled,he] using qu⟩
 
/-- Lift disjointness of the sampler scratch, NTT scratch and output polynomials
into the exact instruction footprint. -/
theorem allWrites_apart {L : KemLay} {kg : Bool} {B : Addr} {r : Region}
    (hs : r.Disjoint ⟨B+BitVec.ofNat 64 (scratchOff kg),2048⟩)
    (hn : r.Disjoint ⟨B+BitVec.ofNat 64 (nttOff kg),1024⟩)
    (ho : ∀j<2*L.k, r.Disjoint ⟨B+BitVec.ofNat 64 (outOff L kg j),1024⟩) :
    ∀q∈allWrites L kg B, r.Disjoint q := by
  intro q hq
  obtain ⟨i,hi,hq⟩ := List.mem_flatMap.mp hq
  have hi' := List.mem_range.mp hi
  simp only [writes,pairWrites,List.mem_cons,List.not_mem_nil,or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hs.sub_right (Offset.sub_base _ (d := 1800) (n := 48) (k := 2048) (by decide))
  · exact hs.sub_right (Region.sub_prefix (by decide : 400≤2048))
  · exact hs.sub_right (Offset.sub_base _ (d := 400) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 528) (n := 128) (k := 2048) (by decide))
  · exact hs.sub_right (Offset.sub_base _ (d := 1536) (n := 136) (k := 2048) (by decide))
  · exact ho _ (by omega)
  · exact ho _ (by omega)
  · exact hn

end VG.Proof.MlKem.AArch64.Noise
