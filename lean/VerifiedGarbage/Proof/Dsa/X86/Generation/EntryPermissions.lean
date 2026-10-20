module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.EntryStart
import VerifiedGarbage.Proof.Framework.Offset

/-! # Narrow the caller's scratch buffer to the subregions required by the proofs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

theorem EntryStart.scratch {s t : State} {A : ParameterABI s} (R : EntryStart A t) {d n : Nat}
    (room : d + n ≤ usedBytes A.geometry.pLen) : InRegions t.wr (off A.geometry.base d) n := by
  refine ⟨_, R.scratchWrite, Offset.contains_base _ ?_ ?_⟩
  · have h := A.arenaRoom
    change d + n ≤ (arg s 11).toNat * 8
    exact Nat.le_trans room h
  · have := A.scratchBound
    have := A.arenaRoom
    change d + n ≤ usedBytes (arg s 2).toNat at room
    omega

theorem EntryStart.covers {s t : State} {A : ParameterABI s} (R : EntryStart A t) :
    Covers (s.rd ++ bodyWrites A) (t.rd ++ t.wr) ∧ Covers (bodyWrites A) t.wr := by
  have writes : Covers (bodyWrites A) t.wr := by
    apply Covers.of_forall
    intro r hr
    simp only [bodyWrites, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Covers.one ⟨_, R.frameWrite, Region.contains_self _ _⟩
    · apply Covers.one
      simpa only [off, BitVec.add_zero] using R.scratch (d := 0) (n := usedBytes A.geometry.pLen) (by omega)
    · exact Covers.one (R.scratch (by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega))
    · exact Covers.one (R.scratch (by unfold VG.Impl.Dsa.Generation.Layout.control usedBytes domainCheck; omega))
    · apply Covers.one
      simpa only [off, BitVec.add_zero] using R.scratch (d := 0) (n := 8192) (by unfold usedBytes domainCheck; omega)
    · exact Covers.one ⟨_, R.outWrite, Region.contains_self _ _⟩
    · exact Covers.one ⟨_, R.argsWrite, Region.contains_self _ _⟩
  exact ⟨Covers.append (by rw [R.rd]; exact Covers.refl _) writes, writes⟩
end VG.Proof.Dsa.X86.Generation
