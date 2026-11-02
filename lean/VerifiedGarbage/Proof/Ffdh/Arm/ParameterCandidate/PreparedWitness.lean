module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput

import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSetup
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Framework.PowLit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SavedFrame
/-! Native Montgomery and exponent preparation establish the complete witness state. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhasePrepared.lean`, which only this module imported.
section

/-! End-to-end native preparation of a q or p phase for the existing shared
Miller–Rabin kernel. Only the phase's scratch and two local counters change. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt arrAt)

private theorem oddThree {n : Nat} (large : 1 < n) (odd : n % 2 = 1) : 3 ≤ n := by omega

private theorem phaseWords {k : Nat} (lower : 64 ≤ k) (upper : k ≤ 1024) :
    4 ≤ Spec.Rsa.modulusWords k ∧ Spec.Rsa.modulusWords k ≤ 128 := by
  simp only [Spec.Rsa.modulusWords]
  omega

theorem phasePrepared_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (stack : Workspace s s.sp 72)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  let w := Spec.Rsa.modulusWords k
  let n := Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared, WP.seq_iff]
  refine WP.mono (montPrep_ok h space) ?_
  rintro u ⟨readyU, dataU, fullU, oneU, minusU, modulusU, r2U, strideU, frameU, restU⟩
  have workspaceU := h.workspace.congr restU.wr
  have stackU : Workspace u u.sp 72 := by rw [restU.sp]; exact stack.congr restU.wr
  have separateU : (⟨State.addr u.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩ := by
    rw [restU.sp]; exact separate
  have smallN : n < 2 ^ (64 * w) := by
    dsimp only [n, w]
    rw [← modulusU]
    exact numAt_lt _ _ _ _
  refine WP.mono (expSetup_ok workspaceU readyU dataU stackU separateU fullU h.large h.odd smallN) ?_
  rintro t ⟨readyT, dataT, exponentT, powerT, arraysT, _, frameT, restT⟩
  have workspaceT := workspaceU.congr restT.wr
  have numbers (j : Nat) (bound : j < 30) (not27 : j ≠ 27) (not29 : j ≠ 29) :
      numAt t.mem (State.addr base) w j = numAt u.mem (State.addr base) w j := by
    rw [← keyView_number_mod t.mem base w j (readyT.baseShiftFits workspaceT),
      ← keyView_number_mod u.mem base w j (readyU.baseShiftFits workspaceU), arraysT j bound not27 not29]
  have dims := phaseWords h.minLength h.maxLength
  have fits : arrAt w 28 ≤ 8 * capacity := readyU.arraysFit (j := 27) (by decide)
  have data : RoundData base capacity w n t.mem :=
    ⟨dataT, dims.1, dims.2, fits, oddThree h.large h.odd, h.odd,
      (numbers 0 (by decide) (by decide) (by decide)).trans modulusU,
      (numbers 4 (by decide) (by decide) (by decide)).trans r2U,
      (numbers 9 (by decide) (by decide) (by decide)).trans oneU,
      (numbers 10 (by decide) (by decide) (by decide)).trans minusU, exponentT, powerT⟩
  rw [restU.sp] at frameT
  exact ⟨data, (frameU.mono (by simp)).trans frameT,
    restU.trans (restT.mono (by simp [roundClobbers, VG.Proof.Rsa.Arm.Keys.opRegs]))⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/PhaseSaved.lean`, which only this module imported.
section

/-! Montgomery and exponent preparation preserve the witness-loop policy slots. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

private theorem locals_disjoint {s : State} {d offset : Nat} (stack : Workspace s s.sp 72)
    (before : d + 4 ≤ offset) (fit : offset + 4 ≤ 72) :
    (⟨State.addr (s.sp + BitVec.ofNat 32 d), 4⟩ : Region).Disjoint
      ⟨State.addr (s.sp + BitVec.ofNat 32 offset), 4⟩ := by
  rw [VG.Arm.addr_add (by have := stack.nowrap; omega), VG.Arm.addr_add (by have := stack.nowrap; omega)]
  exact Offset.disjoint _ (.inl before) (by omega) (by omega)

theorem SavedFrame.after_preparation {s t : State} {base : BitVec 32} {capacity : Nat}
    {values : Nat → BitVec 32} {slots : List Nat} {rs : List Reg}
    (h : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩)
    (changed : Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
      ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem) (rest : Rest rs s t) : SavedFrame values slots t := by
  refine h.after_frame changed rest ?_
  intro d hd r hr
  have fit := bounds d hd
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [VG.Arm.addr_add (by have := h.space.nowrap; omega)]
    exact separate.sub_left (Offset.sub_base _ (by omega))
  · exact locals_disjoint h.space fit (by decide : 60 + 4 ≤ 72)
  · exact locals_disjoint h.space (by omega) (by decide : 64 + 4 ≤ 72)

theorem phasePrepared_saved_ok {s : State} {base src : BitVec 32} {capacity k : Nat}
    {values : Nat → BitVec 32} {slots : List Nat}
    (h : MontPrepInput base src capacity k s) (space : Spec.Rsa.scratchWords k ≤ capacity)
    (saved : SavedFrame values slots s) (bounds : ∀ d ∈ slots, d + 4 ≤ 60)
    (separate : (⟨State.addr s.sp, 72⟩ : Region).Disjoint ⟨State.addr base, 8 * capacity⟩) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      RoundData base capacity (Spec.Rsa.modulusWords k)
        (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr src) k)) t.mem ∧
      SavedFrame values slots t ∧
      Frame [⟨State.addr base, 8 * capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (phasePrepared_ok h space saved.space separate) ?_
  rintro t ⟨data, changed, rest⟩
  exact ⟨data, saved.after_preparation bounds separate changed rest, changed, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm

theorem preparedWitness_ok {s : State} {p : WitnessParams} {src : BitVec 32} {k used : Nat}
    (h : PhaseInput p src k used s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s fun t =>
      WitnessState p used 0 t ∧
      Frame [⟨State.addr p.base, 8 * p.capacity⟩, ⟨State.addr (s.sp + 60#32), 4⟩,
        ⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have bounds : ∀ d ∈ witnessSlots, d + 4 ≤ 60 := by
    intro d hd
    simp only [witnessSlots, List.mem_cons, List.not_mem_nil, or_false] at hd
    omega
  refine WP.mono (phasePrepared_saved_ok h.preparation h.space h.saved bounds h.stackScratch) ?_
  rintro t ⟨data, saved, changed, rest⟩
  rw [h.modulus, ← h.words] at data
  refine ⟨⟨data, h.preparation.workspace.congr rest.wr, saved, ?_, ?_, ?_, h.bitsExact, h.bitsPositive,
    h.bitsBound, h.bitsFit, h.checksPositive, h.checksBound, h.usedBound, Nat.zero_le _,
    h.tapeCount, h.tapeFits, ?_, h.tapeScratch, ?_, ?_, ?_⟩, changed, rest⟩
  · rw [rest.sp]; exact h.stackScratch
  · rw [rest.sp]; exact h.stackBelow
  · rw [rest.sp]; exact h.belowScratch
  · rw [rest.rd, rest.wr]; exact h.tapeRead
  · rw [rest.sp]; exact h.tapeStack
  · rw [rest.sp]; exact h.tapeBelow
  · refine (rsa_bytes_frame changed (by have := h.tapeCount; omega) ?_).trans h.tapeBytes
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact h.tapeScratch
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 60 + 4 ≤ 72))
    · rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
      exact h.tapeStack.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate
