module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPre
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallRegions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallBytes
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! The native search calls its selected, fully verified candidate and restores its live state. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller)

theorem candidateRun_ok (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    {p : SearchParams} {used remaining : Nat} {s : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun (.call backend.candidateName backend.candidate)) s
      fun t => (SearchLive p used remaining t ∧ CandidatePost p used t) ∧ Rest searchClobbers s t := by
  have control : Controller p.control (allocated 24 s) :=
    ⟨⟨p.controlFits, List.mem_cons_of_mem _ h.buffers.controller.space.2⟩, h.buffers.controller.ptr⟩
  have stack : Workspace (allocated 24 s) (allocated 24 s).sp 24 :=
    ⟨callArguments_fits h.buffers.below, List.mem_cons_self⟩
  have separate : (⟨State.addr p.control, 128⟩ : Region).Disjoint
      ⟨State.addr (allocated 24 s).sp, 24⟩ :=
    ((h.buffers.stackSeparate _ (by simp)).2.sub_left (callArguments_sub h.buffers.below)).symm
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun
  refine WP.alloc (by decide) (by have := h.buffers.below; omega) ?_
  rw [WP.seq_iff]
  refine WP.mono (arguments_ok (allocated 24 s) control stack separate h.saved) ?_
  rintro u ⟨⟨args, mem⟩, rest⟩
  have spU : u.sp = s.sp - 24#32 := rest.sp
  have memU : u.mem = callMem p used s.mem (s.sp - 24#32) := mem
  have memAtSp : u.mem = callMem p used s.mem u.sp := by rw [spU]; exact memU
  have facts := h.buffers.callFacts used room
  rw [← spU] at facts
  have writes : Covers (callWr p) u.wr := call_writes
    ⟨p.c.outputFits, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.buffers.output.2⟩
    args.controller.space
    ⟨p.c.scratchFits, by rw [rest.wr]; exact List.mem_cons_of_mem _ h.buffers.scratch.2⟩
  have source : InRegions (u.rd ++ u.wr) (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used) := by
    rw [rest.rd, rest.wr]
    exact InRegions_append_cons.mpr (.inr (h.source_read room))
  refine FrameStack.WP.callF backend.candidate_verified.1 (call_pre facts args memAtSp room)
    (call_reads writes source args.stack) writes (Nat.le_trans backend.candidateStack facts.stackFits) ?_
  intro t rd wr sp frame kept post
  have restored : Rest searchClobbers s (freed 24 t) := by
    refine ⟨?_, rd.trans rest.rd, ?_, ?_⟩
    · intro r hr
      change t.gpr r = s.gpr r
      rw [kept r (by cases r <;> simp_all [searchClobbers, preserved]) (by cases r <;> simp_all [searchClobbers, preserved])]
      exact rest.gpr r (by cases r <;> simp_all [searchClobbers, preserved])
    · change t.wr.tail = s.wr
      rw [wr, rest.wr]
      rfl
    · change t.sp + 24#32 = s.sp
      rw [sp, spU]
      exact BitVec.sub_add_cancel _ _
  have totalFrame : Frame (callChanges p s.sp) s.mem t.mem :=
    (argument_frame h.buffers memU).trans (candidate_frame h.buffers spU backend.candidateStack frame)
  exact ⟨⟨h.after_call restored totalFrame,
    call_post facts args memAtSp (h.call_bytes room memU) post⟩, restored⟩

end VG.Proof.Ffdh.Arm.ParameterSearch
