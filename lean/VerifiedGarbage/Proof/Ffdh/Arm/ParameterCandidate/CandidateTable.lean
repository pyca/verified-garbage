module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
/-! Initialize and run the shared small-prime sieve within candidate buffer bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (arrAt)

theorem candidateTable_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      Frame [⟨State.addr p.base, 8 * p.capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have base : s.mem.readW (State.addr s.sp) 32 = p.base := by
    simpa only [candidateValues, BitVec.add_zero] using h.saved.saved 0 (by simp [candidateSlots])
  have width : s.mem.readW (State.addr (s.sp + 12#32)) 32 = BitVec.ofNat 32 p.length := by
    simpa only [candidateValues] using h.saved.saved 12 (by simp [candidateSlots])
  refine WP.mono (tableWrite_ok h.workspace p.length_bounds.2 p.table_fits
    (by simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide))
    (h.saved.read (by decide)) base width) ?_
  rintro t ⟨table, changed, rest⟩
  have frame : Frame [⟨State.addr p.base, 8 * p.capacity⟩] s.mem t.mem := by
    refine changed.sub ?_
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact ⟨_, by simp, Offset.sub_base _ p.table_fits⟩
  exact ⟨h.after_workspace frame rest, table, frame, rest.mono (by simp [roundClobbers])⟩

theorem CandidateContext.sieve_context {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem) :
    SieveContext p.out p.base p.length s := by
  have fit : arrAt ((p.length + 7) / 8) 34 + 4096 ≤ 8 * p.capacity := p.table_fits
  refine ⟨h.read_context, p.length_bounds.2, ?_, ?_, table, ?_, ?_, h.stackOutput.symm⟩
  · simpa only [candidateValues, BitVec.add_zero] using h.saved.saved 0 (by simp [candidateSlots])
  · exact Nat.le_trans (Nat.add_le_add_left fit p.base.toNat) p.scratchFits
  · intro i hi
    exact h.workspace.read (by have := fit; omega)
  · intro i hi
    exact h.stackScratch.symm.sub_left (Offset.sub_base _ (by have := fit; omega))

end VG.Proof.Ffdh.Arm.ParameterCandidate
