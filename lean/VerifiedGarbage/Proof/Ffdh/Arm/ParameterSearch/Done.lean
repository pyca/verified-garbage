module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions

/-! Assemble the native terminal state from exact policy words, consumed bytes and output. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont
open VG.Proof.Ffdh.Arm.KeySearch (lowWord)

theorem SearchLive.done {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult} {s : State}
    (h : SearchLive p result.used result.remaining s)
    (status : lowWord s.mem p.control 13 = BitVec.ofNat 32 result.status)
    (request : s.mem.readW (off (State.addr p.control) 24) 64 = BitVec.ofNat 64 result.requested)
    (output : searchOutput p result s.mem) : SearchDone p result s := by
  refine ⟨h.buffers, h.usedBound, ?_, ?_, status, ?_, output⟩
  · exact h.saved 6 (by simp [searchSlots])
  · exact h.saved 4 (by simp [searchSlots])
  · change [s.mem.readW (off (State.addr p.control) 0) 64,
      s.mem.readW (off (State.addr p.control) 8) 64,
      s.mem.readW (off (State.addr p.control) 16) 64,
      s.mem.readW (off (State.addr p.control) 24) 64] = _
    have counter := h.counter
    have address : off (State.addr p.control) 0 = State.addr p.control := by simp [off]
    rw [← address] at counter
    rw [counter, h.width, h.entropy, request]
    rfl

theorem control_output {p : SearchParams} {result : Spec.Ffdh.ParameterSearchResult} {m m' : Mem}
    (output : searchOutput p result m) (frame : Frame [⟨State.addr p.control, 128⟩] m m') :
    searchOutput p result m' := by
  unfold searchOutput at output ⊢
  have fit : p.c.out.toNat + p.c.length ≤ 2 ^ 32 := p.c.outputFits
  refine (VG.Proof.Bignum.Arm.rsa_bytes_frame frame (by omega) ?_).trans output
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact p.controlOutput.symm

theorem output_control_word {p : SearchParams} {m m' : Mem} {offset bits : Nat}
    (frame : Frame [⟨State.addr p.c.out, p.c.length⟩] m m')
    (bounds : offset + bits / 8 ≤ 128) :
    m'.readW (off (State.addr p.control) offset) bits = m.readW (off (State.addr p.control) offset) bits := by
  exact frame.readW (r := ⟨State.addr p.control, 128⟩)
    (Offset.contains_base _ bounds (by omega))
    (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact p.controlOutput) (by omega)

end VG.Proof.Ffdh.Arm.ParameterSearch
