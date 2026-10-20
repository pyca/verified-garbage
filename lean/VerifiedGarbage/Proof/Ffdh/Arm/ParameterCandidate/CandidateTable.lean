module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveContext
public import VerifiedGarbage.Proof.Bignum.Arm.RoundState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFrame
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Sieve
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega

/-! Initialize and run the shared small-prime sieve within candidate buffer bounds. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (arrAt)

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
  have fit : arrAt ((p.length + 7) / 8) 34 + 212 ≤ 8 * p.capacity := p.table_fits
  refine ⟨h.read_context, p.length_bounds.2, ?_, ?_, table, ?_, ?_, h.stackOutput.symm⟩
  · simpa only [candidateValues, BitVec.add_zero] using h.saved.saved 0 (by simp [candidateSlots])
  · have := fit
    have := p.scratchFits
    omega
  · intro i hi
    exact h.workspace.read (by have := fit; omega)
  · intro i hi
    exact h.stackScratch.symm.sub_left (Offset.sub_base _ (by have := fit; omega))

theorem candidateSieve_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (large : 8161 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      t.z = Spec.Ffdh.primeShape (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
      Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sieve_shape_ok (h.sieve_context table) large odd) ?_
  rintro t ⟨ctx, flag, changed, rest⟩
  have frame : Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem := changed
  refine ⟨h.after_aux (by decide : 44 ≤ 64) (by decide : 64 + 4 ≤ 68) frame rest,
    ctx.table, flag, ?_, frame, rest.mono (by simp [sieveRegs, roundClobbers])⟩
  refine rsa_bytes_frame frame (by have := p.length_bounds; omega) ?_
  intro r hr
  rw [List.mem_singleton] at hr
  subst r
  rw [VG.Arm.addr_add (by have := h.saved.space.nowrap; omega)]
  exact h.stackOutput.symm.sub_right (Offset.sub_base _ (by decide : 64 + 4 ≤ 72))

end VG.Proof.Ffdh.Arm.ParameterCandidate
