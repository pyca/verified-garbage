module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawSample
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.DrawRange
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Round
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! One complete native witness draw: consume, reject or test, and update status. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def drawPassed (p : WitnessParams) (passed used : Nat) : Nat :=
  if 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1 then
    roundPassed p passed (witnessValue p used) else passed

def drawStatus (p : WitnessParams) (passed used : Nat) : Nat :=
  if 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1 then
    roundStatus p passed (witnessValue p used) else 4

theorem draw_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks)
    (enough : used + (p.bits + 7) / 8 ≤ p.bytes.length) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.draw v.name v.code) s fun t =>
      WitnessState p (used + (p.bits + 7) / 8) (drawPassed p passed used) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (drawStatus p passed used) ∧
      t.z = decide (drawStatus p passed used = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.draw VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (drawRange_ok h enough) ?_)
  rintro u ⟨ctxU, readyU, range, input, frameU, restU⟩
  have word : (u.gpr .r11).toNat =
      if decide (2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1) then 1 else 0 := by
    rw [range]
    by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
    · have valid' : 1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1 := by omega
      simp only [ite_eq_left valid', decide_eq_true valid, ite_true]
      rfl
    · have invalid : ¬ (1 < witnessValue p used ∧ witnessValue p used < p.modulus - 1) := by omega
      simp only [ite_eq_right invalid, decide_eq_false valid, Bool.false_eq_true, ite_false]
      rfl
  refine WP.seq (WP.mono (cmpWord_ok .r11 word) ?_)
  rintro a ⟨⟨zeroA, memA⟩, restA⟩
  have ctxA := ctxU.after_memory memA restA
  have through : Rest roundClobbers s a := restU.trans (restA.mono (by simp [roundClobbers]))
  have frameA : Frame (witnessRegions p s.sp) s.mem a.mem := by rw [memA]; exact frameU
  by_cases valid : 2 ≤ witnessValue p used ∧ witnessValue p used < p.modulus - 1
  · refine WP.seq (WP.ite false (by change some a.z = some false; rw [zeroA, decide_eq_true valid]; rfl)
      (by intro h; cases h) ?_)
    intro _
    have readyA := ctxA.ready ((restA.gpr .r0 (by simp)).trans readyU.ptr)
    refine WP.mono (round_ok v (witness := witnessValue p used) ctxA more readyA (by rw [memA]; exact input)) ?_
    rintro t ⟨stateT, statusT, zeroT, frameT, restT⟩
    rw [through.sp] at frameT
    refine WP.block_nil ?_
    simpa only [drawPassed, drawStatus, ite_eq_left valid] using
      (show WitnessState p (used + (p.bits + 7) / 8) (roundPassed p passed (witnessValue p used)) t ∧
        t.gpr .r3 = BitVec.ofNat 32 (roundStatus p passed (witnessValue p used)) ∧
        t.z = decide (roundStatus p passed (witnessValue p used) = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameA.trans frameT, through.trans restT⟩)
  · refine WP.seq (WP.ite true (by change some a.z = some true; rw [zeroA, decide_eq_false valid]; rfl)
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok a 4 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctxA.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT]; exact frameA
    refine WP.block_nil ?_
    simpa only [drawPassed, drawStatus, ite_eq_right valid] using
      (show WitnessState p (used + (p.bits + 7) / 8) passed t ∧ t.gpr .r3 = BitVec.ofNat 32 4 ∧
        t.z = decide (4 = 4) ∧ Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, through.trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
