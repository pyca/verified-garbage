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
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveInit
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
/-! Initialize and run the shared small-prime sieve within candidate buffer bounds. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Sieve.lean`, which only this module imported.
section

/-! The complete (trialCount n)-prime native sieve implements FFDH's shared primeShape policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Mont VG.Proof.X25519.Arm

theorem sieveLoop_ok {s0 s : State} {dst base : BitVec 32} {n value : Nat}
    (start : SieveInv s0 dst base n value 0 s) :
    WP isa (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep .ne) s (SieveInv s0 dst base n value (trialCount n)) := by
  let inv := fun k t => ∃ i, i + k = (trialCount n) ∧ 0 < k ∧ SieveInv s0 dst base n value i t
  refine WP.loop (M := isa) inv ?_ (trialCount n) s ⟨0, by omega, trialCount_positive n, start⟩
  intro k t h
  obtain ⟨i, hik, positive, state⟩ := h
  have progress := sieveNext_progress (value:=value) (by omega : i < trialCount n)
  refine WP.mono (sieveStep_ok state (by omega)) ?_
  rintro u ⟨next, flag⟩
  by_cases last : sieveNext n value i = trialCount n
  · left
    refine ⟨?_, last ▸ next⟩
    change some (!u.z) = some false
    simp only [flag, last, decide_true, Bool.not_true]
  · right
    refine ⟨?_, trialCount n-sieveNext n value i, by omega,
      sieveNext n value i, by omega, by omega, next⟩
    change some (!u.z) = some true
    simp only [flag, last, decide_false, Bool.not_false]

theorem sieve_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      SieveContext dst base n t ∧
      t.z = !(sieveAny (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) (trialCount n)) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.sieve VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (sieveInit_ok h) ?_)
  intro u start
  refine WP.seq (WP.mono (sieveLoop_ok start) ?_)
  intro v state
  refine WP.seq (WP.mono (sieveFinish_ok state.context.read.frame.space state.bad) ?_)
  rintro t ⟨⟨flag, memory⟩, rest⟩
  refine WP.block_nil ⟨state.context.after_memory memory rest, flag, ?_,
    state.rest.trans (rest.mono (by simp [sieveRegs]))⟩
  rw [memory]
  exact state.changed

theorem sieve_shape_ok {s : State} {dst base : BitVec 32} {n : Nat} (h : SieveContext dst base n s)
    {bits : Nat} (width : n = (bits+7)/8)
    (large : 8161 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      SieveContext dst base n t ∧
      t.z = (Spec.Ffdh.primeShape (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n)) &&
        !Spec.RsaKeyGen.obviouslyComposite bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr dst) n))) ∧
      Frame [sieveLocal s.sp] s.mem t.mem ∧ Rest sieveRegs s t := by
  refine WP.mono (sieve_ok h) ?_
  rintro t ⟨context, flag, changed, rest⟩
  rw [width] at flag
  have shape := sieve_shape (bits:=bits) large odd
  rw [width] at shape
  rw [shape] at flag
  simpa only [width] using And.intro context (And.intro flag (And.intro changed rest))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

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

theorem candidateSieve_ok {s : State} {p : CandidateParams} {consumed : Nat}
    (h : CandidateContext p consumed s) (table : TableData p.base p.length s.mem)
    (large : 8161 < Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length))
    (odd : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) % 2 = 1) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s fun t =>
      CandidateContext p consumed t ∧ TableData p.base p.length t.mem ∧
      t.z = (Spec.Ffdh.primeShape (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)) &&
        !Spec.RsaKeyGen.obviouslyComposite p.bits (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length))) ∧
      Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length ∧
      Frame [⟨State.addr (s.sp + 64#32), 4⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  refine WP.mono (sieve_shape_ok (h.sieve_context table) (bits:=p.bits) rfl large odd) ?_
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
