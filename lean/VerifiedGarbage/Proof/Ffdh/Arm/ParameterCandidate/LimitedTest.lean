module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.LimitedParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseFrame
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessEnd
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseRun
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseHead
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.Block

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
