module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Search writes preserve the complete public entropy tape and caller buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem SearchBuffers.after_frame {p : SearchParams} {s t : State} {rs : List Reg}
    (h : SearchBuffers p s) (kept : .r4 ∉ rs)
    (changed : Frame (searchRegions p s.sp) s.mem t.mem) (rest : Rest rs s t) : SearchBuffers p t := by
  refine ⟨⟨h.controller.space.congr rest.wr, (rest.gpr .r4 kept).trans h.controller.ptr⟩,
    h.output.congr rest.wr, h.used.congr rest.wr, h.scratch.congr rest.wr,
    by rw [rest.rd, rest.wr]; exact h.tapeRead, ?_,
    by rw [rest.sp]; exact h.stack.congr rest.wr, by rw [rest.sp]; exact h.below, ?_⟩
  · refine (rsa_bytes_frame changed (by have := p.c.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    simp only [searchRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact p.c.outputTape.symm
    · exact p.c.tapeScratch
    · exact p.controlTape.symm
    · exact (h.stackSeparate _ (by simp)).2.symm
  · intro r member
    rw [rest.sp]
    exact h.stackSeparate r member

end VG.Proof.Ffdh.Arm.ParameterSearch
