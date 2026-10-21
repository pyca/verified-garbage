module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.MontPrepare
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ExponentSetup
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.KeyView
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Framework.PowLit

/-! End-to-end native preparation of a q or p phase for the existing shared
Miller–Rabin kernel. Only the phase's scratch and two local counters change. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt arrAt)

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
