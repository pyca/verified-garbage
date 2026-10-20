module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PhaseInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTWitnessLoop
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPhasePrepared
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PreparedWitness
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.WitnessState
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

/-! Both native probable-prime phases prepare and draw solely from public inputs. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure PhasePoint where
  params : WitnessParams
  source : BitVec 32
  length : Nat
  used : Nat

def PhaseStart (p : PhasePoint) (s : State) : Prop := PhaseInput p.params p.source p.length p.used s

private def preparationData (p : PhasePoint) : PreparationData :=
  ⟨⟨p.params.base, p.source, p.params.capacity, p.length⟩, p.params.modulus⟩

private theorem phasePreparation_start (p : PhasePoint) (s : State) (h : PhaseStart p s) :
    PreparationStart (preparationData p) s :=
  ⟨⟨h.preparation, h.space⟩, h.saved.space, h.stackScratch, h.modulus⟩

theorem phaseRun_ct (v : RoundImpl) : RelCT isa (Two PhaseStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.phaseRun v.name v.code) (fun _ _ => True) := by
  have prepare : RelCT isa (Two PhaseStart) VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared
      (Two WitnessLoopStart) := by
    have trace := two_map preparationData phasePreparation_start phasePrepared_ct
    have post (p : PhasePoint) (s : State) (h : PhaseStart p s) :
        WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared s
          (WitnessLoopStart ⟨p.params, p.used, 0⟩) :=
      WP.mono (preparedWitness_ok h) (fun _ result => ⟨result.1, h.checksPositive⟩)
    exact (two_post trace post).mono (fun _ _ h => h)
      (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p.params, p.used, 0⟩, left, right, sp⟩)
  exact prepare.seq (millerRabin_ct v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
