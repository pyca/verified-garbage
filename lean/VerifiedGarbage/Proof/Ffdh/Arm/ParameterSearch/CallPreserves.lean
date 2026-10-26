module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import Mathlib.Util.CompileInductive

/-! Candidate calls may overwrite word 14, but preserve the complete retry policy and live headers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

def callChanges (p : SearchParams) (sp : BitVec 32) : List Region :=
  [⟨State.addr p.c.out, p.c.length⟩, ⟨State.addr p.c.base, 8 * p.c.capacity⟩,
    ⟨State.addr (p.control + 112#32), 8⟩, FrameStack.belowA sp 208]

theorem callChanges_sub (p : SearchParams) (sp : BitVec 32) {m m' : Mem}
    (frame : Frame (callChanges p sp) m m') : Frame (searchRegions p sp) m m' := by
  apply frame.sub
  intro r hr
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨_, by simp [searchRegions], fun _ h => h⟩
  · exact ⟨_, by simp [searchRegions], fun _ h => h⟩
  · exact ⟨_, by simp [searchRegions], p.used_sub⟩
  · exact ⟨_, by simp [searchRegions], fun _ h => h⟩

theorem SearchBuffers.call_control {p : SearchParams} {s : State} (h : SearchBuffers p s) :
    ∀ r ∈ callChanges p s.sp, (⟨State.addr p.control, 104⟩ : Region).Disjoint r := by
  intro r hr
  have prefixSub : (⟨State.addr p.control, 104⟩ : Region).Sub ⟨State.addr p.control, 128⟩ :=
    Region.sub_prefix (by decide)
  simp only [callChanges, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact p.controlOutput.sub_left prefixSub
  · exact p.controlScratch.sub_left prefixSub
  · rw [p.used_addr]
    exact VG.Offset.base_disjoint _ (by decide : 104 ≤ 112) (by decide : 112 + 8 ≤ 2 ^ 64)
  · exact ((h.stackSeparate _ (by simp)).2.sub_right prefixSub).symm

theorem SearchLive.after_call {p : SearchParams} {used remaining : Nat} {s t : State}
    (h : SearchLive p used remaining s) (rest : Rest searchClobbers s t)
    (frame : Frame (callChanges p s.sp) s.mem t.mem) : SearchLive p used remaining t := by
  refine ⟨h.buffers.after_frame (by decide) (callChanges_sub p s.sp frame) rest,
    h.usedBound, h.remainingBound, ?_, ?_, ?_, ?_⟩
  · exact (frame.readW (r := ⟨State.addr p.control, 104⟩)
      (by simpa only [off, BitVec.add_zero] using (Offset.contains_base (State.addr p.control)
        (by decide : 0 + 8 ≤ 104) (by decide : 0 < 2 ^ 64))) h.buffers.call_control (by decide)).trans h.counter
  · exact (frame.readW (r := ⟨State.addr p.control, 104⟩)
      (Offset.contains_base _ (by decide : 8 + 8 ≤ 104) (by decide)) h.buffers.call_control (by decide)).trans h.width
  · exact (frame.readW (r := ⟨State.addr p.control, 104⟩)
      (Offset.contains_base _ (by decide : 16 + 8 ≤ 104) (by decide)) h.buffers.call_control (by decide)).trans h.entropy
  · intro j member
    have bound : j ≤ 12 := by
      simp only [searchSlots, List.mem_cons, List.not_mem_nil, or_false] at member
      omega
    exact (frame.readW (r := ⟨State.addr p.control, 104⟩)
      (Offset.contains_base _ (by omega : 8 * j + 4 ≤ 104) (by omega))
      h.buffers.call_control (by decide)).trans (h.saved j member)

end VG.Proof.Ffdh.Arm.ParameterSearch
