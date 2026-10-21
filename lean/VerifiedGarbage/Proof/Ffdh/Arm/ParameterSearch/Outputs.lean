module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.ZeroOutput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPreserves
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Block

/-! Clearing an incomplete or exhausted candidate preserves the search and all policy words. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.X25519.Arm

theorem SearchLive.zero_output {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut s fun t =>
      SearchLive p used remaining t ∧
        Spec.Rsa.bytesAt t.mem (State.addr p.c.out) p.c.length = List.replicate p.c.length 0 ∧
        Frame [⟨State.addr p.c.out, p.c.length⟩] s.mem t.mem ∧ Rest [.r0, .r1, .r2, .lr] s t := by
  have pointer := h.saved 5 (by simp [searchSlots])
  have length := h.saved 1 (by simp [searchSlots])
  simp only [searchValues] at pointer length
  have output : VG.Proof.Ffdh.Arm.OutputBuffer p.c.out p.c.length s :=
    ⟨p.c.outputFits, ⟨_, h.buffers.output.2, Region.contains_self _ _⟩⟩
  refine WP.mono (zeroOut_ok s h.buffers.controller (by have := p.width_bounds; omega)
    (by have := p.width_bounds; omega) pointer length output) ?_
  rintro t ⟨bytes, frame, rest⟩
  exact ⟨h.after_call (rest.mono (by simp [searchClobbers])) (frame.mono (by simp [callChanges])),
    bytes, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
