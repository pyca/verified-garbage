module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.Bignum.Arm.ArithmeticReady
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Spec.Ffdh
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.RoundKernel
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessLocals
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Status
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.OnPass
import VerifiedGarbage.Proof.Ffdh.MillerRabin
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! The selected shared Miller–Rabin round updates native status and success count. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Mont VG.Proof.Bignum.Arm VG.Proof.X25519.Arm
open VG.Proof.Rsa.Mont (numAt)
open VG.Proof.MillerRabin.Arm (RoundImpl)

def roundPassed (p : WitnessParams) (passed witness : Nat) : Nat :=
  if Spec.Ffdh.mrRound p.modulus witness then passed + 1 else passed

def roundStatus (p : WitnessParams) (passed witness : Nat) : Nat :=
  if Spec.Ffdh.mrRound p.modulus witness then (if passed + 1 = p.checks then 1 else 4) else 2

theorem round_ok (v : RoundImpl) {s : State} {p : WitnessParams} {used passed witness : Nat}
    (h : WitnessState p used passed s) (more : passed < p.checks)
    (ready : ArithmeticReady p.base p.capacity p.words s)
    (input : numAt s.mem (State.addr p.base) p.words 1 = witness) :
    WP isa (VG.Impl.Ffdh.Arm.ParameterCandidate.round v.name v.code) s fun t =>
      WitnessState p used (roundPassed p passed witness) t ∧
      t.gpr .r3 = BitVec.ofNat 32 (roundStatus p passed witness) ∧
      t.z = decide (roundStatus p passed witness = 4) ∧
      Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t := by
  have capacity : s.mem.readW (State.addr (s.sp + 36#32)) 32 = BitVec.ofNat 32 p.capacity := by
    simpa only [witnessValues] using h.saved.saved 36 (by simp [witnessSlots])
  unfold VG.Impl.Ffdh.Arm.ParameterCandidate.round VG.Impl.Ffdh.Arm.ParameterCandidate.seqs
  refine WP.seq (WP.mono (roundKernel_ok v ready h.data h.saved.space h.stackScratch capacity
    h.stackBelow h.belowScratch input) ?_)
  rintro u ⟨dataU, valueU, frameU, restU⟩
  have shared : Proof.MillerRabin.Round.round p.modulus witness = Spec.Ffdh.mrRound p.modulus witness := by
    simpa only [Proof.MillerRabin.Round.round] using VG.Proof.Ffdh.rsa_round_eq witness h.data.large h.data.odd
  rw [shared] at valueU
  have ctxU := h.after_round dataU frameU restU
  refine WP.seq (WP.mono (cmpResult_ok valueU) ?_)
  rintro a ⟨⟨zeroA, memA⟩, restA⟩
  have ctxA := ctxU.after_memory memA restA
  have through : Rest roundClobbers s a := restU.trans (restA.mono (by simp [roundClobbers]))
  have frameA : Frame (witnessRegions p s.sp) s.mem a.mem := by
    rw [memA]
    exact frameU.mono (by simp [witnessRegions])
  by_cases pass : Spec.Ffdh.mrRound p.modulus witness = true
  · refine WP.seq (WP.ite false (by change some a.z = some false; rw [zeroA, pass]; rfl)
      (by intro h; cases h) ?_)
    intro _
    have passedWord : a.mem.readW (State.addr (a.sp + 56#32)) 32 = BitVec.ofNat 32 passed := by
      simpa only [witnessValues] using ctxA.saved.saved 56 (by simp [witnessSlots])
    have checksWord : a.mem.readW (State.addr (a.sp + 52#32)) 32 = BitVec.ofNat 32 p.checks := by
      simpa only [witnessValues] using ctxA.saved.saved 52 (by simp [witnessSlots])
    refine WP.mono (onPass_ok ctxA.saved.space more h.checksBound passedWord checksWord) ?_
    rintro t ⟨⟨memT, statusT, zeroT⟩, restT⟩
    have stateT := ctxA.store_passed (by omega : passed + 1 ≤ p.checks) memT restT
    have frameT : Frame [⟨State.addr (s.sp + 56#32), 4⟩] a.mem t.mem := by
      rw [memT, through.sp]
      exact (Frame.refl _ _).writeW (by simp) _ (Region.contains_self _ _)
    refine WP.block_nil ⟨?_, ?_, ?_, frameA.trans (frameT.mono (by simp [witnessRegions])),
      through.trans (restT.mono (by simp [roundClobbers]))⟩
    · simpa only [roundPassed, pass, ite_true] using stateT
    · simpa only [roundStatus, pass, ite_true] using statusT
    · rw [zeroT]
      apply decide_eq_decide.mpr
      by_cases done : passed + 1 = p.checks <;> simp [roundStatus, pass, done]
  · have fail : Spec.Ffdh.mrRound p.modulus witness = false := Bool.eq_false_iff.mpr pass
    refine WP.seq (WP.ite true (by change some a.z = some true; rw [zeroA, fail]; rfl)
      ?_ (by intro h; cases h))
    intro _
    refine WP.mono (setStatus_ok a 2 (by decide)) ?_
    rintro t ⟨⟨statusT, zeroT, memT⟩, restT⟩
    have stateT := ctxA.after_memory memT restT
    have frameT : Frame (witnessRegions p s.sp) s.mem t.mem := by rw [memT]; exact frameA
    refine WP.block_nil ?_
    simpa only [roundPassed, roundStatus, fail, Bool.false_eq_true, ite_false] using
      (show WitnessState p used passed t ∧ t.gpr .r3 = BitVec.ofNat 32 2 ∧ t.z = decide (2 = 4) ∧
        Frame (witnessRegions p s.sp) s.mem t.mem ∧ Rest roundClobbers s t from
        ⟨stateT, statusT, zeroT, frameT, through.trans (restT.mono (by simp [roundClobbers]))⟩)

end VG.Proof.Ffdh.Arm.ParameterCandidate
