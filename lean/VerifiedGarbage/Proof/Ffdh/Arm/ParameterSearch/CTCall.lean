module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTCallState
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTArguments
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPublic
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPre
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallRegions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Tape
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.TCB.Code
public import VerifiedGarbage.Proof.Ffdh.Contract

/-! The selected shared Miller–Rabin candidate is called under its complete public timing contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

private theorem call_ready {q : SearchPoint} {s : State} (h : CallCT q s) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre (callState q.inputs q.used s) ∧
      Covers (callRd q.inputs q.used s.sp ++ callWr q.inputs) (s.rd ++ s.wr) ∧ Covers (callWr q.inputs) s.wr := by
  obtain ⟨original, live, room, args, mem, rest⟩ := h
  have sp : s.sp = original.sp - 24#32 := rest.sp
  have memory : s.mem = callMem q.inputs q.used original.mem s.sp := by rw [sp]; exact mem
  have facts := live.buffers.callFacts q.used room
  rw [← sp] at facts
  have writes : Covers (callWr q.inputs) s.wr := call_writes
    ⟨q.inputs.c.outputFits, by rw [rest.wr]; exact List.mem_cons_of_mem _ live.buffers.output.2⟩
    args.controller.space
    ⟨q.inputs.c.scratchFits, by rw [rest.wr]; exact List.mem_cons_of_mem _ live.buffers.scratch.2⟩
  have source : InRegions (s.rd ++ s.wr) (State.addr (q.inputs.c.tape + BitVec.ofNat 32 q.used))
      (q.inputs.c.bytes.length - q.used) := by
    rw [rest.rd, rest.wr]
    exact InRegions_append_cons.mpr (.inr (live.source_read room))
  exact ⟨call_pre facts args memory room, call_reads writes source args.stack, writes⟩

theorem candidate_call_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    RelCT isa (Two CallCT) (.call backend.candidateName backend.candidate) (fun _ _ => True) := by
  intro s t traceS traceT u v ⟨q, hs, ht, sp⟩ runS runT
  have ct : RelCT isa (fun a b => CallCT q a ∧ CallCT q b ∧ a.sp = s.sp ∧ b.sp = s.sp)
      (.call backend.candidateName backend.candidate) (fun _ _ => True) := by
    refine VG.Arm.RelCT.call backend.candidate_verified.1 backend.candidate_verified.2.1
      (callRd q.inputs q.used s.sp) (callWr q.inputs) ?_
    intro a b ⟨ha, hb, spA, spB⟩
    obtain ⟨preA, readsA, writesA⟩ := call_ready ha
    obtain ⟨preB, readsB, writesB⟩ := call_ready hb
    have pubCall := call_public ha hb (spA.trans spB.symm)
    exact ⟨by simpa only [callState, spA] using preA,
      by simpa only [callState, spB] using preB,
      by simpa only [callState, spA, spB] using pubCall,
      by simpa only [spA] using readsA, writesA, by simpa only [spB] using readsB, writesB⟩
  exact ct _ _ _ _ _ _ ⟨hs, ht, rfl, sp.symm⟩ runS runT

theorem candidate_run_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) :
    RelCT isa (Two ReadyCT)
      (VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun
  apply VG.Proof.Ffdh.Arm.KeySearch.alloc_ct
  refine (RelCT.seq (two_post arguments_ct arguments_ready) (candidate_call_ct backend)).mono ?_ (fun _ _ h => h)
  rintro _ _ ⟨s, t, ⟨q, hs, ht, sp⟩, rfl, rfl⟩
  refine ⟨q, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩, ?_⟩
  change s.sp - 24#32 = t.sp - 24#32
  rw [sp]

end VG.Proof.Ffdh.Arm.ParameterSearch
