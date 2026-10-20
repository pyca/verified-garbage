module

import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Outputs
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.FinishHead
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Ffdh.Arm.Output
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Regions
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Bounds
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.Memory
import VerifiedGarbage.Proof.Framework.Arm.CallF

/-! Storing the consumed-byte count preserves the key pair, retry policy,
and the saved registers needed for the controller's return. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont

structure ResultPost (p : KeyPublic) (result : Spec.Ffdh.KeySearchResult) (s : State) : Prop where
  status : s.gpr .r0 = BitVec.ofNat 32 result.status
  output : KeyOutput p result s.mem
  policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
    [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
      BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)]
  used : Spec.Rsa.wordsAt s.mem (State.addr p.up) 1 = [BitVec.ofNat 64 result.used]

theorem KeyInput.used_separate {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (rX p).Disjoint (rUsed p) ∧ (rY p).Disjoint (rUsed p) ∧ (rControl p).Disjoint (rUsed p) := by
  have pairs := h.layout.pairwise
  rw [← h.layout.wr, h.write_regions] at pairs
  have indexed := List.pairwise_iff_getElem.mp pairs
  exact ⟨indexed 0 2 (by simp) (by simp) (by decide),
    indexed 1 2 (by simp) (by simp) (by decide),
    (indexed 2 4 (by simp) (by simp) (by decide)).symm⟩

theorem KeyInput.saved_used {p : KeyPublic} {s : State} (h : KeyInput p s) :
    (rSaved p).Disjoint (rUsed p) :=
  (h.stack_separate (r := rUsed p) (by rw [h.write_regions]; simp)).sub_left
    (FrameStack.belowA_sub (by decide : 24 ≤ stackUse) h.bounds.stackFits)

theorem KeyDone.used_buffer {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    (h : KeyDone p original result s) : OutputBuffer p.up 8 s := by
  refine ⟨h.input.bounds.usedFit, ⟨rUsed p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyDone.output_after_used {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    {m : Mem} (h : KeyDone p original result s) (frame : Frame [rUsed p] s.mem m) :
    KeyOutput p result m := by
  have xeq := bytesAt_frame (r := rX p) frame (by simpa using h.input.used_separate.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega)
  have yeq := bytesAt_frame (r := rY p) frame (by simpa using h.input.used_separate.2.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega)
  have before := h.output
  cases outcome : result.outcome <;> simp only [KeyOutput, outcome] at before ⊢ <;>
    exact ⟨xeq.trans before.1, yeq.trans before.2⟩

theorem KeyDone.policy_after_used {p : KeyPublic} {original s : State} {result : Spec.Ffdh.KeySearchResult}
    {m : Mem} (h : KeyDone p original result s) (frame : Frame [rUsed p] s.mem m) :
    Spec.Rsa.wordsAt m (State.addr p.control) 4 = Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 := by
  unfold Spec.Rsa.wordsAt
  apply List.map_congr_left
  intro j hj
  have bound : j < 4 := List.mem_range.mp hj
  exact frame.readW (r := rControl p) (Offset.contains_base _ (by omega) (by omega))
    (by simpa using h.input.used_separate.2.2) (by decide)

end VG.Proof.Ffdh.Arm.KeySearch
