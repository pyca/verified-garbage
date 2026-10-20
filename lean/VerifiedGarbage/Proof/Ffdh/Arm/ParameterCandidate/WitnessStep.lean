module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Draw
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! A witness iteration either consumes a nonempty prefix or reports exhausted entropy. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

def witnessNextUsed (p : WitnessParams) (used : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then used + (p.bits + 7) / 8 else used

def witnessNextPassed (p : WitnessParams) (used passed : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then drawPassed p passed used else passed

def witnessNextStatus (p : WitnessParams) (used passed : Nat) : Nat :=
  if used + (p.bits + 7) / 8 ≤ p.bytes.length then drawStatus p passed used else 0

theorem witnessStep_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep v.name v.code) s fun t =>
      WitnessState p (witnessNextUsed p used) (witnessNextPassed p used passed) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (witnessNextStatus p used passed) ∧
      t.z = decide (witnessNextStatus p used passed = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have lengthWord : s.mem.readW (State.addr (s.sp + 20#32)) 32 = BitVec.ofNat 32 p.bytes.length := by
    simpa only [witnessValues] using h.saved.saved 20 (by simp [witnessSlots])
  have usedWord : s.mem.readW (State.addr (s.sp + 40#32)) 32 = BitVec.ofNat 32 used := by
    simpa only [witnessValues] using h.saved.saved 40 (by simp [witnessSlots])
  have widthWord : s.mem.readW (State.addr (s.sp + 48#32)) 32 = BitVec.ofNat 32 ((p.bits + 7) / 8) := by
    simpa only [witnessValues] using h.saved.saved 48 (by simp [witnessSlots])
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (witnessRoom_ok h.saved.space h.tapeCount
    (by have := h.bitsBound; omega) h.usedBound lengthWord usedWord widthWord) ?_)
  rintro u ⟨⟨zero, memory⟩, rest⟩
  have ctx := h.after_memory memory rest
  by_cases enough : used + (p.bits + 7) / 8 ≤ p.bytes.length
  · have available : ¬ p.bytes.length - used < (p.bits + 7) / 8 := by omega
    refine WP.seq (WP.ite false (by change some u.z = some false; rw [zero, decide_eq_false available])
      (by intro h; cases h) ?_)
    intro _
    refine WP.mono (draw_ok v ctx more enough) ?_
    rintro t ⟨stateT, statusT, zeroT, frameT, restT⟩
    rw [rest.sp, memory] at frameT
    refine WP.block_nil ?_
    simpa only [witnessNextUsed, witnessNextPassed, witnessNextStatus, ite_eq_left enough] using
      (show WitnessState p (used + (p.bits + 7) / 8) (drawPassed p passed used) t ∧
        t.gpr .r3 = BitVec.ofNat 32 (drawStatus p passed used) ∧ t.z = decide (drawStatus p passed used = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, (rest.mono (by simp [roundClobbers])).trans restT⟩)
  · have short : p.bytes.length - used < (p.bits + 7) / 8 := by have := h.usedBound; omega
    refine WP.seq (WP.ite true (by change some u.z = some true; rw [zero, decide_eq_true short])
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok u 0 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctx.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT, memory]; exact Frame.refl _ _
    refine WP.block_nil ?_
    simpa only [witnessNextUsed, witnessNextPassed, witnessNextStatus, ite_eq_right enough] using
      (show WitnessState p used passed t ∧ t.gpr .r3 = BitVec.ofNat 32 0 ∧ t.z = decide (0 = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT,
          (rest.mono (by simp [roundClobbers])).trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
