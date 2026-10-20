module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CallPreserves
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.ZeroOutput
import VerifiedGarbage.Proof.Framework.Offset

/-! Clearing both outputs preserves the controller and all loop invariants. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.KeySearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.X25519.Arm (Rest)

theorem KeyLive.x_buffer {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : OutputBuffer p.xp p.len s := by
  refine ⟨h.input.bounds.xFit, ⟨rX p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyLive.y_buffer {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) : OutputBuffer p.yp p.len s := by
  refine ⟨h.input.bounds.yFit, ⟨rY p, ?_, Region.contains_self _ _⟩⟩
  rw [h.wr, h.input.write_regions]
  simp

theorem KeyInput.outputs_control {p : KeyPublic} {s : State} (h : KeyInput p s) :
    ∀ r ∈ [rX p, rY p], (rControl p).Disjoint r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact h.output_regions_disjoint.2.2.2.1
  · exact h.output_regions_disjoint.2.2.2.2.1

theorem KeyLive.zero_outputs {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    (h : KeyLive p original used keys scalars s) :
    WP isa VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs s fun t =>
      KeyLive p original used keys scalars t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.xp) p.len = List.replicate p.len 0 ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.yp) p.len = List.replicate p.len 0 ∧
      Frame [rX p, rY p] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have positive : 0 < p.len := by have := h.input.bounds.minLength; omega
  have fits : p.len < 2 ^ 32 := by have := h.input.bounds.maxLength; omega
  rw [VG.Impl.Ffdh.Arm.KeySearch.zeroOutputs, WP.seq_iff]
  refine WP.mono (zeroOutput_ok s h.controller (by decide : 5 < 16) positive fits
    (h.header (by simp [KeyPublic.headers])) (h.header (by simp [KeyPublic.headers])) h.x_buffer) ?_
  rintro u ⟨xzero, xframe, xrest⟩
  have live : KeyLive p original used keys scalars u :=
    h.restore xrest.rd xrest.wr xrest.sp (fun r hr => xrest.gpr r (by revert r hr; decide))
      (xframe.mono (by simp [callChanges]))
  refine WP.mono (zeroOutput_ok u live.controller (by decide : 6 < 16) positive fits
    (live.header (by simp [KeyPublic.headers])) (live.header (by simp [KeyPublic.headers])) live.y_buffer) ?_
  rintro t ⟨yzero, yframe, yrest⟩
  have finished : KeyLive p original used keys scalars t :=
    live.restore yrest.rd yrest.wr yrest.sp (fun r hr => yrest.gpr r (by revert r hr; decide))
      (yframe.mono (by simp [callChanges]))
  refine ⟨finished, ?_, yzero,
    (xframe.mono (by simp)).trans (yframe.mono (by simp)), xrest.trans yrest⟩
  exact (bytesAt_frame (r := rX p) yframe
    (by simpa using h.input.output_regions_disjoint.1)
    (by change p.len ≤ 2 ^ 64; have := h.input.bounds.maxLength; omega)).trans xzero

theorem KeyOutput.control_frame {p : KeyPublic} {original : State} {result : Spec.Ffdh.KeySearchResult}
    {m m' : Mem} (h : KeyInput p original) (before : KeyOutput p result m)
    (frame : Frame [rControl p] m m') : KeyOutput p result m' := by
  have xeq := bytesAt_frame (r := rX p) frame
    (by simpa using h.output_regions_disjoint.2.2.2.1.symm)
    (by change p.len ≤ 2 ^ 64; have := h.bounds.maxLength; omega)
  have yeq := bytesAt_frame (r := rY p) frame
    (by simpa using h.output_regions_disjoint.2.2.2.2.1.symm)
    (by change p.len ≤ 2 ^ 64; have := h.bounds.maxLength; omega)
  cases outcome : result.outcome <;> simp only [KeyOutput, outcome] at before ⊢ <;>
    exact ⟨xeq.trans before.1, yeq.trans before.2⟩

theorem KeyLive.done {p : KeyPublic} {original s : State} {used keys scalars : Nat}
    {result : Spec.Ffdh.KeySearchResult} (h : KeyLive p original used keys scalars s)
    (count : result.used = used) (status : lowWord s.mem p.control 14 = BitVec.ofNat 32 result.status)
    (policy : Spec.Rsa.wordsAt s.mem (State.addr p.control) 4 =
      [BitVec.ofNat 64 result.retries.keys, BitVec.ofNat 64 result.retries.scalars,
        BitVec.ofNat 64 p.len, BitVec.ofNat 64 (if result.status = 0 then p.len else 0)])
    (output : KeyOutput p result s.mem) : KeyDone p original result s :=
  ⟨h.input, h.rd, h.wr, h.sp, h.pointer, h.kept, h.saved,
    h.header (by simp [KeyPublic.headers]), by rw [count]; exact h.header (by simp [KeyPublic.headers]),
    status, policy, output⟩

end VG.Proof.Ffdh.Arm.KeySearch
