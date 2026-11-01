module

public import VerifiedGarbage.Proof.MlKem.AArch64.Noise.Writes

import VerifiedGarbage.Proof.MlKem.AArch64.Noise.LayoutPair
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Impl.MlKem.AArch64.Noise
import VerifiedGarbage.Proof.MlKem.AArch64.Lay
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Rc4.AArch64.Vec
import VerifiedGarbage.Proof.Sha3.AArch64.Neon.X2Lit
/-! # Complete paired sampling of all secrets and retained errors -/

-- Formerly `VerifiedGarbage/Proof/MlKem/AArch64/Noise/All.lean`, which only this module imported.
section

/-! # Accumulating all paired noise outputs -/
section
namespace VG.Proof.MlKem.AArch64.Noise
open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem

theorem all_loop_ok {s : State} {L : KemLay} (kg : Bool) (hk : 0<L.k)
    (rs : List Region) (out : Nat → Addr) (value : Nat → Poly) (writes : Nat → List Region)
    (hsub : ∀i<L.k, ∀r∈writes i, r∈rs)
    (hfar : ∀i<L.k, ∀j<2*i, ∀r∈writes i, (polyRegion (out j)).Disjoint r)
    (hstep : ∀i<L.k, ∀t, Kept rs s t →
      WP isa (Impl.MlKem.AArch64.Noise.noisePair L kg (2*i)) t fun u =>
        Kept (writes i) t u ∧ PolyIs u.mem (out (2*i)) (value (2*i)) ∧
        PolyIs u.mem (out (2*i+1)) (value (2*i+1))) :
    WP isa (Impl.MlKem.AArch64.Noise.noiseAll L kg) s fun t =>
      Kept rs s t ∧ ∀j<2*L.k, PolyIs t.mem (out j) (value j) := by
  apply WPs.seqs (map_range_ne_nil hk _)
  apply WPs.range (I := fun i t => Kept rs s t ∧ ∀j<2*i, PolyIs t.mem (out j) (value j))
  · intro i hi t ⟨kt,old⟩
    refine WP.mono (hstep i hi t kt) fun u ⟨ku,a,b⟩ => ?_
    refine ⟨kt.trans (ku.mono (hsub i hi)),fun j hj => ?_⟩
    by_cases hj0 : j<2*i
    · exact Proof.MlKem.polyIs_frame ku.frame (hfar i hi j hj0) (old j hj0)
    · rcases (show j=2*i ∨ j=2*i+1 by omega) with rfl | rfl
      · exact a
      · exact b
  · exact ⟨Kept.refl rs s,fun j hj => by omega⟩

end VG.Proof.MlKem.AArch64.Noise
end

end

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
      ∀j<2*L.k, Proof.MlKem.PolyIs t.mem (B+BitVec.ofNat 64 (outOff L kg j))
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
