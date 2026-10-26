module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Policy
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
public import VerifiedGarbage.Impl.Ffdh.Arm.KeySearch
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Framework.Block
import Mathlib.Util.CompileInductive

/-! Exhaustion and entropy requests return zero outputs and exact sampling words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
variable {sampling : VG.Proof.Ffdh.GenerationPolicy}

open VG VG.Arm VG.Proof.Mont VG.Spec.Ffdh

namespace KeyInput
variable {p : KeyPublic sampling} {s : State} {m m' : Mem}

theorem outputs_low_frame (h : KeyInput p s) (frame : Frame [rX p, rY p] m m')
    (j : Nat) (bound : j < 16) : lowWord m' p.control j = lowWord m p.control j :=
  frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
    h.outputs_control (by decide)

theorem outputs_high_frame (h : KeyInput p s) (frame : Frame [rX p, rY p] m m')
    (j : Nat) (bound : j < 16) :
    m'.readW (off (State.addr p.control) (8 * j + 4)) 32 =
      m.readW (off (State.addr p.control) (8 * j + 4)) 32 :=
  frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
    h.outputs_control (by decide)

theorem outputs_policy_frame (h : KeyInput p s) (frame : Frame [rX p, rY p] m m') :
    Spec.Rsa.wordsAt m' (State.addr p.control) 4 = Spec.Rsa.wordsAt m (State.addr p.control) 4 := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < 4 := List.mem_range.mp hj
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
    h.outputs_control (by decide)

end KeyInput

def exhaustedResult (used : Nat) : KeySearchResult := ⟨.exhausted, used, []⟩
def requestResult (used keys scalars : Nat) : KeySearchResult := ⟨.entropy ⟨keys, scalars⟩, used, []⟩

theorem KeyLive.exhausted {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.exhausted s (KeyDone p original (exhaustedResult used)) := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.exhausted, WP.seq_iff]
  refine WP.mono (h.terminal (status := 3) (.inr rfl)) ?_
  rintro t ⟨live, status, request, high, _⟩
  have sampling := live.policy (request := 0) (by decide) request high
  refine WP.mono live.zero_outputs ?_
  rintro q ⟨done, xzero, yzero, frame, _⟩
  apply done.done (result := exhaustedResult used) rfl
  · exact (h.input.outputs_low_frame frame 14 (by decide)).trans status
  · exact (h.input.outputs_policy_frame frame).trans sampling
  · exact ⟨xzero, yzero⟩

theorem KeyLive.request {p : KeyPublic sampling} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.request s (KeyDone p original (requestResult used keys scalars)) := by
  rw [VG.Impl.Ffdh.Arm.KeySearch.request, WP.seq_iff]
  refine WP.mono h.request_block ?_
  rintro t ⟨live, status, request, high⟩
  have sampling := live.policy (request := p.len) (by have := h.input.bounds.maxLength; omega) request high
  refine WP.mono live.zero_outputs ?_
  rintro q ⟨done, xzero, yzero, frame, _⟩
  apply done.done (result := requestResult used keys scalars) rfl
  · exact (h.input.outputs_low_frame frame 14 (by decide)).trans status
  · exact (h.input.outputs_policy_frame frame).trans sampling
  · exact ⟨xzero, yzero⟩

end VG.Proof.Ffdh.Arm.KeySearch
