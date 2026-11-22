module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTCallState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTArguments
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Call
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTFrames
import VerifiedGarbage.Proof.Framework.Arm.RelCT
public import VerifiedGarbage.TCB.Code
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTLeaf
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTRequest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CompareResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.LivePolicy
meta import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
meta import VerifiedGarbage.Proof.Framework.Arm.Taint
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
meta import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CTState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Live
meta import VerifiedGarbage.Proof.Ffdh.Contract

/-! ### `Ffdh.Arm.ParameterSearch.CTClassify`, which only this module used -/

section

/-! Candidate classification and entropy exhaustion branch only on the public tape and policy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_piece two_ite)

def EntropyCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧
  isa.eval .eq s = some (decide (q.inputs.c.bytes.length - q.used < Spec.Ffdh.parameterEntropy q.inputs.c.bits))

private theorem entropy_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 2] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s (EntropyCT q) := by
  refine WP.mono h.entropy_guard ?_
  rintro t ⟨⟨live, flag, _⟩, _⟩
  exact ⟨live, by change some t.z = _; rw [flag]⟩

theorem short_ct : RelCT isa (Two LiveCT) VG.Impl.Ffdh.Arm.ParameterSearch.short (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.short
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) entropy_ready) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact request_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)
  · exact exhausted_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
      ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1⟩, ⟨q.used, q.remaining, ht.1.1⟩, sp⟩) (fun _ _ h => h)

def PostCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧ CandidatePost q.inputs q.used s

def ComparisonCT (test : Nat) (q : SearchPoint) (s : State) : Prop := PostCT q s ∧
  isa.eval .eq s = some (decide (Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used) = test))

private theorem compare_ready (test : Nat) (which : test = 1 ∨ test = 2)
    (q : SearchPoint) (s : State) (h : PostCT q s) :
    WP isa (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) s (ComparisonCT test q) := by
  have small : Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used) < 3 := by
    cases candidateResult q.inputs q.used with
    | none => decide
    | some pair => obtain ⟨prime, rand⟩ := pair; cases prime <;> simp only [Proof.Ffdh.candidateStatus] <;> decide
  have value : s.gpr .r0 = BitVec.ofNat 32 (Proof.Ffdh.candidateStatus (candidateResult q.inputs q.used)) := by
    rw [← h.2.status, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  refine WP.mono (compareResult_ok s small which value) ?_
  rintro t ⟨⟨flag, mem⟩, rest⟩
  exact ⟨⟨h.1.after_read (by decide) mem rest, h.2.after_read mem rest (by decide)⟩,
    by change some t.z = _; rw [flag]⟩

private theorem compare_ct (test : Nat) (which : test = 1 ∨ test = 2) :
    RelCT isa (Two PostCT) (.block [.cmp .r0 (.imm (BitVec.ofNat 32 test))]) (Two (ComparisonCT test)) := by
  rcases which with rfl | rfl
  all_goals exact two_piece [] (by intro _ _ _ _ _ r hr; cases hr) (by taint_decide) (compare_ready _ (by decide))

theorem classify_ct : RelCT isa (Two PostCT) VG.Impl.Ffdh.Arm.ParameterSearch.classify (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.classify
  refine RelCT.seq (compare_ct 1 (Or.inl rfl)) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · exact accepted_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
      ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1.1⟩, ⟨q.used, q.remaining, ht.1.1.1⟩, sp⟩) (fun _ _ h => h)
  · refine RelCT.seq ((compare_ct 2 (Or.inr rfl)).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)) ?_
    refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
    · exact rejected_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
        ⟨q.inputs, ⟨q.used, q.remaining, hs.1.1.1⟩, ⟨q.used, q.remaining, ht.1.1.1⟩, sp⟩) (fun _ _ h => h)
    · exact short_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1.1, ht.1.1.1, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.CTCall`, which only this module used -/

section

/-! ### `Ffdh.Arm.ParameterSearch.CallPublic`, which only this module used -/

section

/-! Equal public search positions supply equal public candidate arguments and entropy suffixes. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem call_public {q : SearchPoint} {s t : State} (hs : CallCT q s) (ht : CallCT q t) (sp : s.sp = t.sp) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 232).pub (callState q.inputs q.used s) (callState q.inputs q.used t) := by
  obtain ⟨originalS, liveS, roomS, argsS, memS, restS⟩ := hs
  obtain ⟨originalT, liveT, roomT, argsT, memT, restT⟩ := ht
  have spS : s.sp = originalS.sp - 24#32 := restS.sp
  have spT : t.sp = originalT.sp - 24#32 := restT.sp
  have memoryS : s.mem = callMem q.inputs q.used originalS.mem s.sp := by rw [spS]; exact memS
  have memoryT : t.mem = callMem q.inputs q.used originalT.mem t.sp := by rw [spT]; exact memT
  have factsS := liveS.buffers.callFacts q.used roomS
  have factsT := liveT.buffers.callFacts q.used roomT
  rw [← spS] at factsS
  rw [← spT] at factsT
  have a0S := call_stackArg (j := 0) factsS.argsFits memoryS (by decide)
  have a1S := call_stackArg (j := 1) factsS.argsFits memoryS (by decide)
  have a2S := call_stackArg (j := 2) factsS.argsFits memoryS (by decide)
  have a3S := call_stackArg (j := 3) factsS.argsFits memoryS (by decide)
  have a4S := call_stackArg (j := 4) factsS.argsFits memoryS (by decide)
  have a0T := call_stackArg (j := 0) factsT.argsFits memoryT (by decide)
  have a1T := call_stackArg (j := 1) factsT.argsFits memoryT (by decide)
  have a2T := call_stackArg (j := 2) factsT.argsFits memoryT (by decide)
  have a3T := call_stackArg (j := 3) factsT.argsFits memoryT (by decide)
  have a4T := call_stackArg (j := 4) factsT.argsFits memoryT (by decide)
  simp only [callValue] at a0S a1S a2S a3S a4S a0T a1T a2T a3T a4T
  have bytesS := liveS.call_bytes roomS memS
  have bytesT := liveT.call_bytes roomT memT
  have tapeNat : (BitVec.ofNat 32 (q.inputs.c.bytes.length - q.used)).toNat = q.inputs.c.bytes.length - q.used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := q.inputs.c.tapeCount; omega_using [this])]
  simp only [State.addr] at bytesS bytesT
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [argsS.out, argsS.width, argsS.usedPtr, argsS.bits,
    argsT.out, argsT.width, argsT.usedPtr, argsT.bits,
    a0S, a1S, a2S, a3S, a4S, a0T, a1T, a2T, a3T, a4T, tapeNat]
  rw [bytesS, bytesT]
  simp only [sp, true_and]

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end


/-! The selected shared Miller–Rabin candidate is called under its complete public timing contract. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

private theorem call_ready {q : SearchPoint} {s : State} (h : CallCT q s) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 232).pre (callState q.inputs q.used s) ∧
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

end

end


/-! The native search step selects its public entropy-length path and calls the proved candidate. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_piece two_post two_ite)

def LengthCT (q : SearchPoint) (s : State) : Prop := LiveCT q s ∧
  isa.eval .eq s = some (decide (q.inputs.c.bytes.length - q.used < q.inputs.c.length))

private theorem length_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa (.block ([VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r9 10,
      VG.Impl.Ffdh.Arm.ParameterSearch.ldf .r10 1] ++ VG.Impl.Ffdh.Arm.ParameterSearch.less)) s (LengthCT q) := by
  refine WP.mono h.length_guard ?_
  rintro t ⟨⟨live, flag, _⟩, _⟩
  exact ⟨live, by change some t.z = _; rw [flag]⟩

private theorem zero_ready (q : SearchPoint) (s : State) (h : LiveCT q s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut s (LiveCT q) :=
  WP.mono h.zero_output fun _ ⟨live, _⟩ => live

private theorem run_ready (backend : VG.Proof.Ffdh.Arm.ParameterBackend)
    (q : SearchPoint) (s : State) (h : ReadyCT q s) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterSearch.candidateRun (.call backend.candidateName backend.candidate)) s (PostCT q) :=
  WP.mono (candidateRun_ok backend h.1 h.2) fun _ ⟨data, _⟩ => data

theorem step_ct (backend : VG.Proof.Ffdh.Arm.ParameterBackend) : RelCT isa (Two LiveCT)
    (VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep (.call backend.candidateName backend.candidate)) (fun _ _ => True) := by
  unfold VG.Impl.Ffdh.Arm.ParameterSearch.candidateStep
  refine RelCT.seq (two_piece [.r4] live_pins (by taint_decide) length_ready) ?_
  refine two_ite (fun _ _ _ hs ht => hs.2.trans ht.2.symm) ?_ ?_
  · have zeroTrace : RelCT isa (Two LiveCT) VG.Impl.Ffdh.Arm.ParameterSearch.zeroOut (fun _ _ => True) :=
      zero_ct.mono (fun _ _ ⟨q, hs, ht, sp⟩ =>
        ⟨q.inputs, ⟨q.used, q.remaining, hs⟩, ⟨q.used, q.remaining, ht⟩, sp⟩) (fun _ _ h => h)
    exact (RelCT.seq (two_post zeroTrace zero_ready) request_ct).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, hs.1.1, ht.1.1, sp⟩) (fun _ _ h => h)
  · have ready (q : SearchPoint) (s : State) (h : LengthCT q s ∧ isa.eval .eq s = some false) : ReadyCT q s := by
      have enough := of_decide_eq_false (Option.some.inj (h.1.2.symm.trans h.2))
      exact ⟨h.1.1, by have := h.1.1.usedBound; omega_using [enough, this]⟩
    exact (RelCT.seq (two_post (candidate_run_ct backend) (run_ready backend)) classify_ct).mono
      (fun _ _ ⟨q, hs, ht, sp⟩ => ⟨q, ready q _ hs, ready q _ ht, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterSearch
