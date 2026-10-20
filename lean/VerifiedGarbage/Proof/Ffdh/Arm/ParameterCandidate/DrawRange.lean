module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.InRange
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Rejection-sample the imported witness against the shared FFDH range check. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt)

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
