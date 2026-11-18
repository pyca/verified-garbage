module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterBackend
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPost
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterSearch
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallGeometry
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallParams
import VerifiedGarbage.Proof.Framework.Block
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.CallPreserves
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.State
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterSearch.Bounds
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Framework.Arm.Call
public import VerifiedGarbage.Spec.Ffdh.SievedContract
import VerifiedGarbage.Proof.Framework.CallLay

/-! ### `Ffdh.Arm.ParameterSearch.CallRegions`, which this module and modules that import it used -/

section

/-! The candidate's narrowed permissions are covered by the controller's buffers. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm

theorem call_writes {p : SearchParams} {s : State}
    (output : Workspace s p.c.out p.c.length)
    (control : Workspace s p.control 128)
    (scratch : Workspace s p.c.base (8 * p.c.capacity)) : Covers (callWr p) s.wr := by
  apply Covers.cons (Covers.one ⟨_, output.2, Region.contains_self _ _⟩)
  apply Covers.cons ?_ (Covers.one ⟨_, scratch.2, Region.contains_self _ _⟩)
  apply Covers.one
  rw [p.used_addr]
  exact VG.CallLay.inRegions_sub ⟨_, control.2, Region.contains_self _ _⟩
    (by decide : 112 + 8 ≤ 128) (by decide)

theorem call_reads {p : SearchParams} {used : Nat} {s : State}
    (writes : Covers (callWr p) s.wr)
    (source : InRegions (s.rd ++ s.wr) (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used)) (stack : Workspace s s.sp 24) :
    Covers (callRd p used s.sp ++ callWr p) (s.rd ++ s.wr) := by
  apply Covers.append_left ?_ writes.right
  apply Covers.pair (Covers.one source)
  apply Covers.right
  apply Covers.one
  simpa only [VG.Proof.Mont.off, BitVec.add_zero] using VG.CallLay.inRegions_sub
    ⟨_, stack.2, Region.contains_self _ _⟩ (off := 0) (by decide : 0 + 20 ≤ 24) (by decide)

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.CallPre`, which this module and modules that import it used -/

section

/-! The nested native candidate satisfies the existing public FFDH signature's precondition. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem call_pre {p : SearchParams} {used : Nat} {s : State} {m : Mem}
    (facts : CallFacts p used s.sp) (context : ArgumentContext p used s)
    (memory : s.mem = callMem p used m s.sp) (room : used + p.c.length ≤ p.c.bytes.length) :
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre (callState p used s) := by
  let q := p.candidateParams used room
  have a0 := call_stackArg (j := 0) facts.argsFits memory (by decide)
  have a1 := call_stackArg (j := 1) facts.argsFits memory (by decide)
  have a2 := call_stackArg (j := 2) facts.argsFits memory (by decide)
  have a3 := call_stackArg (j := 3) facts.argsFits memory (by decide)
  have a4 := call_stackArg (j := 4) facts.argsFits memory (by decide)
  simp only [callValue] at a0 a1 a2 a3 a4
  have widthNat : (BitVec.ofNat 32 p.c.length).toNat = p.c.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.width_bounds; omega_using [this])]
  have bitsNat : (BitVec.ofNat 32 p.c.bits).toNat = p.c.bits := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.maxBits; omega_using [this])]
  have genNat : (BitVec.ofNat 32 p.c.generator).toNat = p.c.generator := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.c.generatorAllowed with eq | eq <;> omega_using [eq])]
  have tapeNat : (BitVec.ofNat 32 (p.c.bytes.length - used)).toNat = p.c.bytes.length - used := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.c.tapeCount; omega_using [this])]
  have capNat : (BitVec.ofNat 32 p.c.capacity).toNat = p.c.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.capacity_fits]
  sig_pre [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  simp only [context.out, context.width, context.usedPtr, context.bits,
    a0, a1, a2, a3, a4, widthNat, bitsNat, genNat, tapeNat, capNat]
  have argAddr : stackArgAddr (callState p used s) 0 = State.addr s.sp := by simp [stackArgAddr]
  rw [argAddr]
  simp only [Nat.mul_comm p.c.capacity 8]
  have address := FrameStack.addr_sub' facts.stackFits
  change BitVec.setWidth 64 (s.sp - 184#32) = BitVec.setWidth 64 s.sp - 184#64 at address
  rw [← address]
  refine ⟨facts.stackFits, facts.argsFits, rfl, rfl, q.outputUsed, ?_, q.outputScratch,
    facts.outputArgs, ?_, q.usedScratch, facts.usedArgs, ?_, facts.scratchArgs,
    facts.stackOutput, facts.stackUsed, facts.stackTape, facts.stackScratch, facts.stackArgs,
    q.outputFits, q.usedFits, ?_, q.scratchFits, p.c.minBits, p.c.maxBits, rfl, p.c.generatorAllowed, p.c.space⟩
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.outputTape
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.usedTape
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.tapeScratch
  · simpa only [q, SearchParams.candidateParams, VG.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams.length, State.addr, List.length_drop] using q.tapeFits

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! ### `Ffdh.Arm.ParameterSearch.CallBytes`, which this module and modules that import it used -/

section

/-! Preparing stack arguments leaves the remaining candidate entropy unchanged. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm

theorem SearchLive.call_bytes {p : SearchParams} {used remaining : Nat} {s u : State}
    (h : SearchLive p used remaining s) (room : used + p.c.length ≤ p.c.bytes.length)
    (mem : u.mem = callMem p used s.mem (s.sp - 24#32)) :
    Spec.Rsa.bytesAt u.mem (State.addr (p.c.tape + BitVec.ofNat 32 used))
      (p.c.bytes.length - used) = p.c.bytes.drop used := by
  rw [mem]
  refine (rsa_bytes_frame (callMem_frame p used s.mem (s.sp - 24#32))
    (by have := p.c.tapeCount; omega_using [this]) ?_).trans (h.source_bytes room)
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact (((h.buffers.stackSeparate _ (by simp)).2.sub_left
    (callArguments_sub h.buffers.below)).sub_right (p.source_sub used room)).symm

end VG.Proof.Ffdh.Arm.ParameterSearch

end

end

/-! The native search calls its selected, fully verified candidate and restores its live state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterSearch/CallFrame.lean`, which only this module imported.
section

/-! Argument stores and candidate stack writes stay below the search's saved frame. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm

theorem argument_frame {p : SearchParams} {used : Nat} {s u : State}
    (h : SearchBuffers p s) (mem : u.mem = callMem p used s.mem (s.sp - 24#32)) :
    Frame (callChanges p s.sp) s.mem u.mem := by
  rw [mem]
  apply (callMem_frame p used s.mem (s.sp - 24#32)).sub
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  exact ⟨_, by simp [callChanges], callArguments_sub h.below⟩

theorem candidate_frame {p : SearchParams} {s u t : State} {depth : Nat}
    (h : SearchBuffers p s) (sp : u.sp = s.sp - 24#32) (limit : depth ≤ 184)
    (frame : Frame (callWr p ++ [FrameStack.belowA u.sp depth]) u.mem t.mem) :
    Frame (callChanges p s.sp) u.mem t.mem := by
  apply frame.sub
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · simp only [callWr, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    all_goals exact ⟨_, by simp [callChanges], fun _ h => h⟩
  · obtain rfl := List.mem_singleton.mp hr
    refine ⟨FrameStack.belowA s.sp 208, by simp [callChanges], ?_⟩
    rw [sp]
    exact fun a ha => callStack_sub h.below a
      (FrameStack.belowA_sub limit (callStack_fits h.below) a ha)

end VG.Proof.Ffdh.Arm.ParameterSearch
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterSearch
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Controller)

/-- A register the search keeps is one the callee preserves, and none of the
arguments' registers. -/
private theorem searchKept {r : Reg} (hr : r ∉ searchClobbers) :
    r ∈ preserved ∧ r ≠ .lr ∧ r ∉ ([.r0, .r1, .r2, .r3, .r9, .r12] : List Reg) := by
  revert hr; cases r <;> decide

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
  refine WP.alloc (by decide) (by have := h.buffers.below; omega_using [this]) ?_
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
  intro t rd wr sp frame kept post lm lu hfl
  have argsSub := callArguments_sub h.buffers.below
  have restored : Rest searchClobbers s { freed 24 t with mem := lm, unknowns := lu } := by
    refine ⟨?_, rd.trans rest.rd, ?_, ?_⟩
    · intro r hr
      change t.gpr r = s.gpr r
      obtain ⟨k₁, k₂, k₃⟩ := searchKept hr
      rw [kept r k₁ k₂]
      exact rest.gpr r k₃
    · change t.wr.tail = s.wr
      rw [wr, rest.wr]
      rfl
    · change t.sp + 24#32 = s.sp
      rw [sp, spU]
      exact BitVec.sub_add_cancel _ _
  have totalFrame : Frame (callChanges p s.sp) s.mem lm :=
    ((argument_frame h.buffers memU).trans (candidate_frame h.buffers spU backend.candidateStack frame)).trans
      (hfl.sub fun r hr => ⟨FrameStack.belowA s.sp 208, by simp [callChanges], by
        obtain rfl := List.mem_singleton.mp hr; exact argsSub⟩)
  have cp := call_post facts args memAtSp (h.call_bytes room memU) post
  have outSep := ((h.buffers.stackSeparate ⟨State.addr p.c.out, p.c.length⟩ (by simp)).2.sub_left argsSub).symm
  have usedSep := (((h.buffers.stackSeparate ⟨State.addr p.control, 128⟩ (by simp)).2.sub_left argsSub).symm.sub_left
    p.used_sub)
  refine ⟨⟨h.after_call restored totalFrame, ⟨cp.status, ?_, ?_⟩⟩, restored⟩
  · refine Eq.trans (VG.Proof.Bignum.Arm.rsa_bytes_frame hfl
      (by have fit : p.c.out.toNat + p.c.length ≤ 2 ^ 32 := p.c.outputFits; omega_using [fit])
      fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact outSep) cp.output
  · refine Eq.trans ?_ cp.consumed
    unfold Spec.Rsa.wordsAt
    apply List.map_congr_left
    intro j hj
    have bound : j < 1 := List.mem_range.mp hj
    exact hfl.readW (r := ⟨State.addr (p.control + 112#32), 8⟩)
      (Offset.contains_base _ (by omega_using [bound]) (by omega_using [bound]))
      (fun r hr => by obtain rfl := List.mem_singleton.mp hr; exact usedSep) (by decide)

end VG.Proof.Ffdh.Arm.ParameterSearch
