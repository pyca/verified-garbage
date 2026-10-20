module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawHead
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SampleWitness
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessTape
import VerifiedGarbage.Proof.Framework.Arm.Exec

/-! Draw, consume, import and mask one public witness prefix. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Spec.Rsa.Mont (numAt)

def witnessValue (p : WitnessParams) (used : Nat) : Nat :=
  Spec.Rsa.os2ip ((p.bytes.drop used).take ((p.bits + 7) / 8)) % 2 ^ p.bits

theorem drawSample_ok {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) passed t ∧ ArithmeticReady p.base p.capacity p.words t ∧
      numAt t.mem (State.addr p.base) p.words 1 = witnessValue p used ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  rw [VG.Impl.Ffdh.Arm.ParameterCandidate.drawSample, WP.seq_iff]
  refine WP.mono (drawHead_ok h enough) ?_
  rintro u ⟨ctx, base, source, count, changed, rest⟩
  have bits : u.mem.readW (State.addr (u.sp + 44#32)) 32 = BitVec.ofNat 32 p.bits := by
    simpa only [witnessValues] using ctx.saved.saved 44 (by simp [witnessSlots])
  refine WP.mono (sampleWitness_ok (ctx.ready base) ctx.data ctx.saved.space ctx.stackScratch
    ctx.bitsPositive ctx.bitsBound ctx.bitsFit bits (ctx.source_fits enough) (ctx.source_read enough)
    (ctx.source_separate enough) source count) ?_
  rintro t ⟨readyT, dataT, value, _, changedT, restT⟩
  rw [ctx.source_bytes enough] at value
  exact ⟨ctx.after_workspace dataT changedT restT, readyT, value,
    (changed.mono (by simp [witnessRegions])).trans (changedT.mono (by simp [witnessRegions])), rest.trans restT⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
