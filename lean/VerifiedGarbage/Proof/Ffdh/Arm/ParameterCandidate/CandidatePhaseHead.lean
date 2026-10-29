module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePhaseMath
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseHeader
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Bignum.Arm.Workspace
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhasePieces
/-! Initialize the q/p policy without changing candidate metadata or entropy accounting. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhaseHead.lean`, which only this module imported.
section

/-! Compose the native policy setup for q and p. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Proof.Bignum.Arm (Workspace)

theorem phaseHead_ok (q : Bool) (s : State) {bits : Nat} (lower : 512 ≤ bits) (upper : bits ≤ 8192)
    (space : Workspace s s.sp 72)
    (value : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 bits) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      (t.mem = phaseMemory s q bits) ∧ Rest [.r1, .r3, .r4, .r5, .r12] s t := by
  have read24 : InRegions (s.rd ++ s.wr) (State.addr (s.sp + 24#32)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.read (by decide)
  have writes (d : Nat) (bound : d + 4 ≤ 72) : InRegions s.wr (State.addr (s.sp + BitVec.ofNat 32 d)) 4 := by
    rw [VG.Arm.addr_add (by have := space.nowrap; omega)]
    exact space.write bound
  have phasePositive : 0 < phaseBits q bits := by cases q <;> simp [phaseBits] <;> omega
  have phaseBound : phaseBits q bits ≤ 8192 := by cases q <;> simp [phaseBits] <;> omega
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead
  simp only [List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (phaseBitHead_ok q s (by omega) read24 (writes 44 (by decide)) value) ?_
  rintro u ⟨⟨bitValue, memU⟩, restU⟩
  rw [WP.block_append_iff]
  refine WP.mono (phaseWidth_ok u phaseBound bitValue (by rw [restU.wr, restU.sp]; exact writes 48 (by decide))) ?_
  rintro v ⟨memV, restV⟩
  rw [WP.block_append_iff]
  have stable : v.gpr .r3 = BitVec.ofNat 32 (phaseBits q bits) := (restV.gpr .r3 (by simp)).trans bitValue
  refine WP.mono (phaseChecks_ok v phasePositive phaseBound stable (by
    rw [restV.wr, restU.wr, restV.sp, restU.sp]; exact writes 52 (by decide))) ?_
  rintro w ⟨memW, restW⟩
  refine WP.mono (phasePassed_ok w (by
    rw [restW.wr, restV.wr, restU.wr, restW.sp, restV.sp, restU.sp]; exact writes 56 (by decide))) ?_
  rintro t ⟨memT, restT⟩
  refine ⟨?_, (restU.mono (by simp)).trans ((restV.mono (by simp)).trans
    ((restW.mono (by simp)).trans (restT.mono (by simp))))⟩
  rw [memT, memW, memV, memU, restW.sp, restV.sp, restU.sp]
  rfl

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem candidatePhaseHead_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (q : Bool) :
    WP isa (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseHead q)) s fun t =>
      CandidateContext p consumed t ∧
      SavedFrame (witnessValues (candidatePhase p q) consumed 0) witnessSlots t ∧
      Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have bits : s.mem.readW (State.addr (s.sp + 24#32)) 32 = BitVec.ofNat 32 p.bits :=
    h.saved.saved 24 (by decide)
  refine WP.mono (phaseHead_ok q s p.minBits p.maxBits h.saved.space bits) ?_
  rintro t ⟨memory, rest⟩
  have changed : Frame [⟨State.addr (s.sp + 44#32), 16⟩] s.mem t.mem := by
    rw [memory]
    exact phaseMemory_frame q p.bits h.saved.space.nowrap
  have candidateChanged : Frame (candidateRegions p s.sp) s.mem t.mem := by
    refine changed.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    refine ⟨⟨State.addr (s.sp + 40#32), 28⟩, by simp [candidateRegions], ?_⟩
    rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega), VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
    exact Offset.sub _ (by decide) (by decide)
  have context : CandidateContext p consumed t := by
    refine h.after_frame h.consumedBound ?_ candidateChanged rest
    rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide : 40 + 4 ≤ 72) (by decide)]
    exact h.saved.saved 40 (by decide)
  refine ⟨context, ⟨?_, ?_⟩, changed, rest.mono (by simp [roundClobbers])⟩
  · rw [rest.sp]
    exact h.saved.space.congr rest.wr
  · intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rw [rest.sp, memory, phaseMemory_word h.saved.space.nowrap (by decide) (by decide)]
    all_goals first | rfl | exact h.saved.saved _ (by decide)

end VG.Proof.Ffdh.Arm.ParameterCandidate
