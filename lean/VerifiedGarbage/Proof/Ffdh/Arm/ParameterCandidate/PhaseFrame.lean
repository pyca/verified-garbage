module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! A complete phase may update its local policy words, scratch, and callee stack. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

def phaseRegions (p : WitnessParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.base, 8 * p.capacity⟩, FrameStack.belowA sp 56, ⟨State.addr (sp + 40#32), 28⟩]

private theorem local_sub {s : State} {d : Nat} (stack : Workspace s s.sp 72)
    (lower : 40 ≤ d) (upper : d + 4 ≤ 68) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Sub ⟨State.addr (s.sp + 40#32), 28⟩ := by
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.sub _ lower (by omega)

theorem phase_preparation_frame {s t : State} {p : WitnessParams} (stack : Workspace s s.sp 72)
    (changed : Frame [⟨State.addr p.base, 8 * p.capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem) : Frame (phaseRegions p s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨⟨State.addr p.base, 8 * p.capacity⟩, by simp [phaseRegions], fun _ h => h⟩
  · exact ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [phaseRegions], local_sub stack (by decide) (by decide)⟩
  · exact ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [phaseRegions], local_sub stack (by decide) (by decide)⟩

theorem phase_witness_frame {s t : State} {p : WitnessParams} (stack : Workspace s s.sp 72)
    (changed : Frame (witnessRegions p s.sp) s.mem t.mem) : Frame (phaseRegions p s.sp) s.mem t.mem := by
  refine changed.sub ?_
  intro r hr
  simp only [witnessRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨⟨State.addr p.base, 8 * p.capacity⟩, by simp [phaseRegions], fun _ h => h⟩
  · exact ⟨FrameStack.belowA s.sp 56, by simp [phaseRegions], fun _ h => h⟩
  · exact ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [phaseRegions], local_sub stack (by decide) (by decide)⟩
  · exact ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [phaseRegions], local_sub stack (by decide) (by decide)⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
