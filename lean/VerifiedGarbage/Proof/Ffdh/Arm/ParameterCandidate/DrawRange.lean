module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawSample

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundData
import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Impl.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.Range
import VerifiedGarbage.Proof.Ffdh.Arm.Checks
import VerifiedGarbage.Proof.Ffdh.Arm.SetLowBit
import VerifiedGarbage.Proof.Bignum.Arm.SmallConst
import VerifiedGarbage.Proof.Bignum.Arm.HeaderStore
import VerifiedGarbage.Proof.Framework.Omega
/-! Rejection-sample the imported witness against the shared FFDH range check. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/InRange.lean`, which only this module imported.
section

/-! Reuse FFDH's existing witness range-check proof, strengthening it with
preservation of the shared primality round's extended-array constants. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt Operand)

private theorem greaterOne_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.greaterOne 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.greaterOne, WP.seq_iff]
  refine WP.mono (smallConst_ok s 1 ready (o := 7) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, _, _, keepsU, _, _⟩
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  refine WP.mono (compare_ok u readyU (a := 7) (b := 1) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨readyT, _, keepsT, _, _⟩
  exact ⟨readyT, dataU.after_operand (by decide) (by decide) (by decide) keepsT⟩

private theorem saveFlag_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (.block VG.Impl.Ffdh.Arm.saveFlag) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  have size : 256 ≤ 8 * capacity :=
    Nat.le_trans (Nat.le_add_right 256 (28 * (8 * (w + 2)))) data.fits
  unfold VG.Impl.Ffdh.Arm.saveFlag
  refine wp_str (a := off (State.addr base) 136) (by decide)
    (by rw [ready.ptr]; exact VG.Arm.addr_add (by have := ready.workspace.nowrap; omega))
    (ready.workspace.write (by omega)) fun t store => WP.block_nil ?_
  have rest : Rest [] s t := store.rest []
  have result := ready.after_header (d := 136) (by decide) (by decide) store.mem rest
    ((rest.gpr .r0 (by simp)).trans ready.ptr)
  refine ⟨result.1, ?_⟩
  rw [store.mem]
  exact data.after_aux_word (by decide) (by decide) _

private theorem belowP_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.belowP 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.belowP, WP.seq_iff]
  refine WP.mono (VG.Proof.Ffdh.Arm.copy_ok s ready (o := 7) (a := 1) (by decide) (by decide) (by decide)) ?_
  rintro u ⟨readyU, _, keepsU, _, _⟩
  have dataU := data.after_operand (by decide) (by decide) (by decide) keepsU
  rw [WP.seq_iff]
  refine WP.mono (VG.Proof.Ffdh.Arm.setLowBit_ok u readyU) ?_
  rintro v ⟨readyV, _, keepsV, _, _⟩
  have dataV := dataU.after_operand (by decide) (by decide) (by decide) keepsV
  refine WP.mono (compare_ok v readyV (a := 7) (b := 0) (by decide) (by decide) (by decide) (by decide)) ?_
  rintro t ⟨readyT, _, keepsT, _, _⟩
  exact ⟨readyT, dataV.after_operand (by decide) (by decide) (by decide) keepsT⟩

private theorem inRange_data {s : State} {base : BitVec 32} {capacity w n : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s fun t => RoundData base capacity w n t.mem := by
  rw [VG.Impl.Ffdh.Arm.inRange, WP.seq_iff]
  refine WP.mono (greaterOne_data ready data) ?_
  rintro u ⟨readyU, dataU⟩
  rw [WP.seq_iff]
  refine WP.mono (saveFlag_data readyU dataU) ?_
  rintro v ⟨readyV, dataV⟩
  rw [WP.seq_iff]
  refine WP.mono (belowP_data readyV dataV) ?_
  rintro a ⟨readyA, dataA⟩
  refine WP.mono (VG.Proof.Ffdh.Arm.andFlag_ok a readyA) ?_
  rintro t ⟨⟨_, mem⟩, _⟩
  exact mem ▸ dataA

theorem inRangeWitness_ok {s : State} {base : BitVec 32} {capacity w n witness : Nat}
    (ready : ArithmeticReady base capacity w s) (data : RoundData base capacity w n s.mem)
    (input : numAt s.mem (State.addr base) w 1 = witness) :
    WP isa (VG.Impl.Ffdh.Arm.inRange 1) s fun t =>
      ArithmeticReady base capacity w t ∧ RoundData base capacity w n t.mem ∧
      t.gpr .r11 = (if 1 < witness ∧ witness < n - 1 then 1 else 0) ∧
      numAt t.mem (State.addr base) w 1 = witness ∧
      Frame [⟨State.addr base, 8 * capacity⟩] s.mem t.mem ∧ Rest roundClobbers s t := by
  have operand : Operand 1 := by simp [Operand, Proof.Rsa.Mont.aAcc, Proof.Rsa.Mont.aTmp]
  refine WP.mono ((VG.Proof.Ffdh.Arm.inRange_ok s ready operand (by decide)
    (by rw [data.modulus]; exact data.odd)).and (inRange_data ready data)) ?_
  rintro t ⟨⟨readyT, flag, arrays, frame, rest⟩, dataT⟩
  rw [input, data.modulus] at flag
  exact ⟨readyT, dataT, flag, (arrays 1 operand (by decide)).trans input, frame, rest⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt)

theorem drawRange_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧ ArithmeticReady p.base p.capacity p.words t ∧
      t.gpr .r11 = (if 1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1 then 1 else 0) ∧
      numAt t.mem (State.addr p.base) p.words 1 = witnessValue p used ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange, WP.seq_iff]
  refine WP.mono (drawSample_ok h enough) ?_
  rintro u ⟨ctx, ready, value, changed, rest⟩
  refine WP.mono (inRangeWitness_ok ready ctx.data value) ?_
  rintro t ⟨readyT, dataT, flag, valueT, changedT, restT⟩
  exact ⟨ctx.after_workspace dataT changedT restT, readyT, flag, valueT,
    changed.trans (changedT.mono (by simp [witnessRegions])), rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
