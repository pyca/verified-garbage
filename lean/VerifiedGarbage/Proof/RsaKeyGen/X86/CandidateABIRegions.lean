module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABIGeometry
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABISeparate
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateABITable

/-! # The ABI's reserved stack contains both candidate frames and the saved registers -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86

theorem CallLayout.writeMember {s : State} (A : CallLayout s) {r : Region}
    (mem : r ∈ (callEnvironment s).writeRegions) : r ∈ s.wr := by
  rw [A.wr]
  exact List.mem_append_left _ mem

theorem CallSeparation.stackAll {s : State} (_A : CallLayout s) (D : CallSeparation s) :
    ∀ r ∈ (callEnvironment s).writeRegions ++ (callEnvironment s).readRegions, r.Disjoint (reservedRegion s) := by
  intro r mem
  rcases List.mem_append.mp mem with mem | mem
  · exact D.stackFar r (List.mem_append_left _ mem)
  · change r ∈ inputRegions (callEnvironment s) ++ [(callEnvironment s).tableRegion] at mem
    rcases List.mem_append.mp mem with mem | mem
    · exact D.stackFar r (List.mem_append_right _ mem)
    · obtain rfl := List.mem_singleton.mp mem
      exact D.tableProperties.2.2.2

theorem CallSeparation.readWriteAll {s : State} (A : CallLayout s) (D : CallSeparation s) :
    ∀ r ∈ (callEnvironment s).readRegions, ∀ R ∈ (callEnvironment s).writeRegions, r.Disjoint R := by
  intro r mem R write
  change r ∈ inputRegions (callEnvironment s) ++ [(callEnvironment s).tableRegion] at mem
  rcases List.mem_append.mp mem with mem | mem
  · exact D.readWrite r mem R write
  · obtain rfl := List.mem_singleton.mp mem
    exact D.tableProperties.2.1 R (A.writeMember write)

theorem CallLayout.savedSub {s : State} (A : CallLayout s) :
    (⟨(callEnvironment s).p.setWidth 64, 16⟩ : Region).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 152 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_sub (by decide) A.low

theorem CallLayout.bodyStackSub {s : State} (A : CallLayout s) :
    (below (callEnvironment s).p 136).Sub (reservedRegion s) := by
  have reserved : reservedRegion s = below (s.gpr .esp) 152 := by
    unfold reservedRegion below
    rw [Taint.sub_setWidth A.low]
  rw [reserved]
  exact below_inner (by decide) A.low

theorem call_args_address (s : State) : ((callEnvironment s).p + 20#32).setWidth 64 = argAddr s 0 := by
  change ((s.gpr .esp - 16#32 + 20#32).setWidth 64) = ((s.gpr .esp + 4#32).setWidth 64)
  congr 1
  rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

end VG.Proof.RsaKeyGen.X86.Candidate
