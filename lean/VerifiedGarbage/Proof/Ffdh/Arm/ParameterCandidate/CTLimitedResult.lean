module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTExponentLoop
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Framework.Arm.Exec
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Framework.RelCT
public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ShapeOdd
public import VerifiedGarbage.Proof.Ffdh.ParameterCandidate.ShapeOctets
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedProject
import VerifiedGarbage.Proof.Dsa.PackedBytes
import VerifiedGarbage.Proof.Framework.CallLay
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X25519.Arm.Instr
import VerifiedGarbage.Proof.Bignum.Octets
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseRun
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block

/-! ### `Ffdh.Arm.ParameterCandidate.LimitedTest`, which this module and modules that import it used -/

section

/-! ### `Ffdh.Arm.ParameterCandidate.LimitedHead`, which this module and modules that import it used -/

section

/-! Limit a prepared p header while preserving all candidate metadata and tape counters. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/LimitStore.lean`, which only this module imported.
section

/-! The native header limits the first p phase to one round or subtracts that round. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem phaseLimit_ok (first : Bool) {s : State} {checks : Nat} (positive : 0 < checks)
    (stack : Workspace s s.sp 72)
    (saved : s.mem.readW (State.addr (s.sp + 52#32)) 32 = BitVec.ofNat 32 checks) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s fun t =>
      t.mem = s.mem.writeW (State.addr (s.sp + 52#32)) (BitVec.ofNat 32 (limitedChecks first checks)) ∧
      Rest [.r1, .r12] s t := by
  have read : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 52#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.read (by decide)
  have write : InRegions s.wr (State.addr (s.sp + 52#32)) 4 := by
    rw [VG.Arm.addr_add (by have := stack.nowrap; omega)]
    exact stack.write (by decide)
  have subtract : BitVec.ofNat 32 checks - 1 = BitVec.ofNat 32 (checks - 1) :=
    BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) positive
  refine withRest_all [.r1, .r12] ?_ (by cases first <;> rfl) (by rfl)
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit VG.Impl.Ffdh.Arm.ParameterCandidate.save limitedChecks
  cases first <;> ffrun [List.cons_append, List.nil_append, BitVec.add_zero, read, write, saved, subtract]
  all_goals rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem limitedHead_ok {s : State} {p : CandidateParams} {used : Nat}
    (h : CandidateContext p used s) (first : Bool) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead false ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s fun t =>
      CandidateContext p used t ∧ SavedFrame (witnessValues (limitedPhase p first) used 0) witnessSlots t ∧
      Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [WP.block_append_iff]
  refine WP.mono (candidatePhaseHead_ok h false) ?_
  rintro u ⟨ctx, saved, changed, rest⟩
  have checks : 0 < Spec.Ffdh.primeChecks p.bits := by unfold Spec.Ffdh.primeChecks; split <;> decide
  refine WP.mono (phaseLimit_ok first checks ctx.saved.space (saved.saved 52 (by decide))) ?_
  rintro t ⟨memory, restT⟩
  have frame : Frame [⟨State.addr (u.sp + 44#32), 16⟩] u.mem t.mem := by
    rw [memory]
    refine (Frame.refl _ _).writeW (r := ⟨State.addr (u.sp + 44#32), 16⟩) (by simp) _ ?_
    rw [VG.Arm.addr_add (by have := ctx.saved.space.nowrap; omega_using [this]),
      VG.Arm.addr_add (by have := ctx.saved.space.nowrap; omega_using [this])]
    exact Offset.contains _ (by decide) (by decide) (by decide)
  have usedWord : t.mem.readW (State.addr (t.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    rw [restT.sp, memory, phaseStore_word _ _ ctx.saved.space.nowrap (by decide) (by decide) (by decide) _]
    exact ctx.saved.saved 40 (by decide)
  have phaseFrame := candidate_header_frame (p := p) (q := false) ctx.saved.space.nowrap frame
  refine ⟨ctx.after_frame ctx.consumedBound usedWord (candidate_phase_frame phaseFrame) restT, ?_, ?_,
    rest.trans (restT.mono (by simp [roundClobbers]))⟩
  · refine ⟨by rw [restT.sp]; exact saved.space.congr restT.wr, ?_⟩
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [restT.sp, memory, phaseStore_word _ _ ctx.saved.space.nowrap (by decide) (by decide) (by decide) _]
    all_goals first | rfl | exact saved.saved _ (by decide)
  · rw [rest.sp] at frame
    exact changed.trans frame

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! One limited p batch with exact shared witness-stream consumption. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def LimitedTestEnd (p : CandidateParams) (first : Bool) (used : Nat) (s t : State) : Prop :=
  ∃ next, CandidateContext p next t ∧ used ≤ next ∧
    t.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (witnessRemaining (limitedPhase p first) used 0)) ∧
    (∀ pass rest, witnessRemaining (limitedPhase p first) used 0 = some (pass, rest) → rest = p.bytes.drop next) ∧
    Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
    Frame (phaseRegions (limitedPhase p first) s.sp) s.mem t.mem ∧ Rest roundClobbers s t

theorem limitedTest_ok (v : RoundImpl) {s : State} {p : CandidateParams} {consumed : Nat} {first : Bool}
    (h : CandidateContext p consumed s)
    (number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (limitedPhase p first).modulus)
    (odd : (limitedPhase p first).modulus % 2 = 1) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) s (LimitedTestEnd p first consumed s) := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited, WP.seq_iff]
  refine WP.mono (limitedHead_ok h first) ?_
  rintro u ⟨context, saved, changed, rest⟩
  have phaseFrame := candidate_header_frame (p := p) (q := false) h.saved.space.nowrap changed
  have bytes := h.phase_output phaseFrame
  have numberU : Spec.Rsa.os2ip (Spec.Rsa.bytesAt u.mem (State.addr p.out) p.length) =
      (limitedPhase p first).modulus := by rw [bytes]; exact number
  refine WP.mono (phaseRun_ok v (candidatePhaseInputWithChecks context saved numberU (p.limited_bounds first).1 (p.limited_bounds first).2 odd)) ?_
  rintro t ⟨next, passed, state, consumedT, status, suffix, changedT, restT⟩
  have bytesT := context.phase_output (q := false) changedT
  have contextT := context.after_frame state.usedBound (state.saved.saved 40 (by decide))
    (candidate_phase_frame (p := p) (q := false) changedT) restT
  rw [rest.sp] at changedT
  exact ⟨next, contextT, consumedT, status, suffix, bytesT.trans bytes, phaseFrame.trans changedT, rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CandidateShape`, which the modules that import this one used -/

section

/-! Candidate shaping draws exactly the first p-width bytes of the original tape. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Shape.lean`, which only this module imported.
section

/-! Complete native shaping of the first candidate drawn from the tape. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Ffdh.ParameterCandidate (topCut topCut_length lastOne_length shapedOctets shapedOctets_value)

private def shapeRegs : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .lr]

theorem shapeP_ok (s : State) {dst src : BitVec 32} {bs : List Byte} {bits : Nat}
    (h : ShapeContext dst src bs bits s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP s fun t =>
      ShapeContext dst src bs bits t ∧
      Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = shapedOctets bs ((bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length) =
        VG.Spec.Ffdh.candidateOf bits (Spec.Rsa.os2ip bs) ∧
      Frame [⟨State.addr dst, bs.length⟩] s.mem t.mem ∧
      Rest [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r9, .lr] s t := by
  have size := h.size
  have nonempty : bs ≠ [] := by intro nil; simp only [nil, List.length_nil] at size; omega
  have bitBound := Nat.mod_lt (bits - 1) (by decide : 0 < 8)
  have cutLength := topCut_length nonempty ((bits - 1) % 8)
  have cutNonempty : topCut bs ((bits - 1) % 8) ≠ [] := by simp [topCut]
  have shapedLength : (shapedOctets bs ((bits - 1) % 8)).length = bs.length :=
    (lastOne_length cutNonempty).trans cutLength
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (shapeCopy_ok s h) ?_)
  rintro u ⟨contextU, copied, frameU, restU⟩
  refine WP.seq (WP.mono (shapeMasks_ok u (by have := h.minBits; omega) (by have := h.maxBits; omega)
    (contextU.frame.read (d := 24) (by decide)) (contextU.frame.saved 24 (by decide))) ?_)
  rintro v ⟨mask, memory, restV⟩
  have contextV := contextU.after_memory memory restV
  have bytesV : ∀ i < bs.length, v.mem (State.addr (dst + BitVec.ofNat 32 i)) = bs[i]?.getD 0 := by
    intro i hi
    rw [memory]
    exact copied i hi
  refine WP.seq (WP.mono (shapeTop_ok v contextV bitBound bytesV mask) ?_)
  rintro w ⟨contextW, destW, bytesW, frameW, restW⟩
  refine WP.seq (WP.mono (shapeOdd_ok w contextW cutLength (by
    intro i hi
    simpa only [List.getD_eq_getElem?_getD] using bytesW i hi) destW) ?_)
  rintro t ⟨contextT, bytesT, frameT, restT⟩
  have encoding : Spec.Rsa.bytesAt t.mem (State.addr dst) bs.length = shapedOctets bs ((bits - 1) % 8) := by
    apply List.ext_getElem
    · rw [VG.Proof.Bignum.bytesAt_length]
      exact shapedLength.symm
    · intro i hi hi'
      have bound : i < bs.length := by rwa [VG.Proof.Bignum.bytesAt_length] at hi
      have byte := bytesT i bound
      rw [VG.Arm.addr_add (by have := h.destFits; omega)] at byte
      simp only [Spec.Rsa.bytesAt, List.getElem_map, List.getElem_range]
      change t.mem (State.addr dst + BitVec.ofNat 64 i) =
        (shapedOctets bs ((bits - 1) % 8)).getD i 0 at byte
      simpa only [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi', Option.getD_some] using byte
  have frameV : Frame [⟨State.addr dst, bs.length⟩] s.mem v.mem := by
    rw [memory]
    exact frameU
  have restUV : Rest shapeRegs s v := (restU.mono (by simp [shapeRegs])).trans (restV.mono (by simp [shapeRegs]))
  have restUW : Rest shapeRegs s w := restUV.trans (restW.mono (by simp [shapeRegs]))
  refine WP.block_nil ⟨contextT, encoding, ?_, (frameV.trans frameW).trans frameT,
    restUW.trans (restT.mono (by simp [shapeRegs]))⟩
  rw [encoding, shapedOctets_value (bits := bits) (j := (bits - 1) % 8) nonempty bitBound (by have := h.length; have := h.minBits; omega)]

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.ParameterCandidate (shapedOctets)

theorem CandidateContext.shape_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (enough : p.length ≤ p.bytes.length) :
    ShapeContext p.out p.tape (p.bytes.take p.length) p.bits s := by
  have size : (p.bytes.take p.length).length = p.length := by rw [List.length_take, Nat.min_eq_left enough]
  refine ⟨h.saved.project ?_ ?_, by have := p.minBits; omega_using [this], p.maxBits, size, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [shapeSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [candidateSlots]
  · intro d hd
    rw [size]
    simp only [shapeSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> rfl
  · rw [size]
    have := p.tapeFits
    omega_using [enough, this]
  · rw [size]
    exact p.outputFits
  · rw [size]
    simpa only [BitVec.add_zero] using CallLay.inRegions_sub h.tapeRead
      (off := 0) (by omega_using [enough] : 0 + p.length ≤ p.bytes.length) (by have := p.tapeCount; omega_using [this])
  · rw [size]
    exact h.outputWrite
  · rw [size]
    exact p.outputTape.symm.sub_left (Region.sub_prefix enough)
  · rw [size]
    exact h.stackOutput.symm
  · rw [size]
    have slice := VG.Proof.Dsa.bytesAt_slice s.mem (State.addr p.tape)
      (offset := 0) (len := p.length) (by omega_using [enough] : 0 + p.length ≤ p.bytes.length)
    simpa only [List.drop_zero, BitVec.add_zero, h.tapeBytes] using slice.symm

theorem candidateShape_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (enough : p.length ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP s fun t =>
      CandidateContext p consumed t ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length =
        shapedOctets (p.bytes.take p.length) ((p.bits - 1) % 8) ∧
      Spec.Rsa.os2ip (Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length) = p.candidate ∧
      Frame [⟨State.addr p.out, p.length⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (shapeP_ok s (h.shape_context enough)) ?_
  rintro t ⟨_, bytes, value, changed, rest⟩
  have size : (p.bytes.take p.length).length = p.length := by rw [List.length_take, Nat.min_eq_left enough]
  rw [size] at bytes value changed
  exact ⟨h.after_output changed rest, bytes, value, changed, rest.mono (by simp [roundClobbers])⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! ### `Ffdh.Arm.ParameterCandidate.CTLimitedTest`, which this module and modules that import it used -/

section

/-! The first or remaining p witness batch has a public trace. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def limitedPhasePoint (first : Bool) (p : CandidatePoint) : PhasePoint :=
  ⟨limitedPhase p.params first, p.params.out, p.params.length, p.used⟩

private theorem limitedPhaseStart_ok (first : Bool) (p : CandidatePoint) (s : State) (h : CandidateTestStart false p s) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead false ++
      VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) s (PhaseStart (limitedPhasePoint first p)) := by
  refine WP.mono (limitedHead_ok h.1 first) ?_
  rintro t ⟨context, saved, changed, _⟩
  have phaseFrame := candidate_header_frame (p := p.params) (q := false) h.1.saved.space.nowrap changed
  have bytes := h.1.phase_output phaseFrame
  exact candidatePhaseInputWithChecks context saved (by rw [bytes]; exact h.2.1)
    (p.params.limited_bounds first).1 (p.params.limited_bounds first).2 h.2.2

theorem limitedTest_ct (v : RoundImpl) (first : Bool) : RelCT isa (Two (CandidateTestStart false))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) (fun _ _ => True) := by
  have limitTrace : RelCT isa (fun s t => s.sp = t.sp)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseLimit first)) (fun s t => s.sp = t.sp) := by
    cases first <;> exact RelCT.block_append
      ((VG.Proof.Bignum.Arm.stackOnly_ct _ rfl).seq (save_ct .r1 52))
  have headerTrace := RelCT.block_append ((phaseHead_ct false).seq limitTrace)
  have head := two_post (headerTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
    (limitedPhaseStart_ok first)
  exact head.seq ((phaseRun_ct v).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨limitedPhasePoint first p, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate

end

end

/-! Return a public witness-engine answer regardless of which batch produced it. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateAnswerResult (answer : CandidatePoint → Option (Bool × List Byte)) (p : CandidatePoint) (s : State) : Prop :=
  (∃ next, CandidateContext p.params next s) ∧ s.gpr .r3 = BitVec.ofNat 32 (witnessResultStatus (answer p))

def limitedAnswer (first : Bool) (p : CandidatePoint) : Option (Bool × List Byte) :=
  witnessRemaining (limitedPhase p.params first) p.used 0

theorem limitedTestResult_ct (v : RoundImpl) (first : Bool) : RelCT isa (Two (CandidateTestStart false))
    (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first v.name v.code) (Two (CandidateAnswerResult (limitedAnswer first))) :=
  two_post (limitedTest_ct v first) (fun _ _ h => WP.mono (limitedTest_ok v h.1 h.2.1 h.2.2)
    (fun _ ⟨next, ctx, _, status, _, _, _, _⟩ => ⟨⟨next, ctx⟩, status⟩))

theorem candidateAnswerResult_ct (answer : CandidatePoint → Option (Bool × List Byte)) :
    RelCT isa (Two (CandidateAnswerResult answer)) VG.Impl.Ffdh.Arm.ParameterCandidate.result (fun _ _ => True) := by
  refine two_map (fun p => (⟨p.params.out, p.params.usedPtr, p.params.length⟩, witnessResultStatus (answer p))) ?_ result_ct
  intro p s h
  obtain ⟨next, ctx⟩ := h.1
  exact ⟨⟨next, ctx.result_context⟩, witnessResultStatus_bound _, h.2⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
