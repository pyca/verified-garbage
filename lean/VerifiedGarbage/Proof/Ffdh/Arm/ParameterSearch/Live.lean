module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Memory
import VerifiedGarbage.Proof.Framework.Offset

/-! Read-only blocks and writes confined to the native controller preserve search buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem SearchLive.after_read {p : SearchParams} {used remaining : Nat} {s t : State} {rs : List Reg}
    (h : SearchLive p used remaining s) (kept : .r4 ∉ rs) (mem : t.mem = s.mem)
    (rest : Rest rs s t) : SearchLive p used remaining t := by
  have frame : Frame (searchRegions p s.sp) s.mem t.mem := by rw [mem]; exact Frame.refl _ _
  exact ⟨h.buffers.after_frame kept frame rest, h.usedBound, h.remainingBound,
    by rw [mem]; exact h.counter, by rw [mem]; exact h.width, by rw [mem]; exact h.entropy,
    by rw [mem]; exact h.saved⟩

theorem SearchLive.after_control {p : SearchParams} {used remaining nextUsed nextRemaining : Nat}
    {s t : State} {rs : List Reg} (h : SearchLive p used remaining s) (kept : .r4 ∉ rs)
    (frame : Frame [⟨State.addr p.control, 128⟩] s.mem t.mem) (rest : Rest rs s t)
    (usedBound : nextUsed ≤ p.c.bytes.length) (remainingBound : nextRemaining ≤ p.attempts)
    (counter : t.mem.readW (State.addr p.control) 64 = BitVec.ofNat 64 nextRemaining)
    (width : t.mem.readW (off (State.addr p.control) 8) 64 = BitVec.ofNat 64 p.c.length)
    (entropy : t.mem.readW (off (State.addr p.control) 16) 64 =
      BitVec.ofNat 64 (Spec.Ffdh.parameterEntropy p.c.bits))
    (saved : ∀ j ∈ searchSlots, VG.Proof.Ffdh.Arm.KeySearch.lowWord t.mem p.control j = searchValues p nextUsed j) :
    SearchLive p nextUsed nextRemaining t :=
  ⟨h.buffers.after_frame kept (frame.mono (by simp [searchRegions])) rest,
    usedBound, remainingBound, counter, width, entropy, saved⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
