module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairTrials
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrials
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveControl
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_ite)

private def PairDone (p : PairData × Nat) (s : State) : Prop :=
  s.z=(Spec.Rsa.os2ip p.1.bytes%VG.Impl.RsaKeyGen.tabEntry p.2==0 ||
    (VG.Impl.RsaKeyGen.tabEntry p.2-1+Spec.Rsa.os2ip p.1.bytes)%VG.Impl.RsaKeyGen.tabEntry p.2==0)

theorem pairActiveStep_ct : RelCT isa (Two PairTrialsStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairActiveStep (fun _ _ => True) := by
  have trials : RelCT isa (Two PairTrialsStart) VG.Impl.Ffdh.Arm.ParameterCandidate.pairTrials (Two PairDone) :=
    two_post pairTrials_ct (fun p s h => by
      refine WP.mono (pairTrials_ok h.context h.index h.cursor (by rw [h.bytes])) ?_
      rintro t ⟨flag,_,_⟩
      exact flag)
  have flag : RelCT isa (Two PairDone) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFlag (fun s t => s.sp=t.sp) :=
    sieveFlag_ct.mono (fun _ _ ⟨_,a,b,sp⟩ => ⟨sp,a.trans b.symm⟩) (fun _ _ h => h)
  have count : RelCT isa (fun s t => s.sp=t.sp)
      (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.pairAdvance ++ VG.Impl.Ffdh.Arm.ParameterCandidate.sieveCount))
      (fun s t => s.sp=t.sp) := stackOnly_ct _ rfl
  exact trials.seq (flag.seq (count.seq (RelCT.block_nil (fun _ _ _ => trivial))))

structure PairStepStart (p : PairData × Nat) (s : State) : Prop where
  trials : PairTrialsStart p s
  bad : s.mem.readW (State.addr (s.sp+64#32)) 32 = if pairAny (Spec.Rsa.os2ip p.1.bytes) p.2 then 1 else 0

private def PairGuarded (p : PairData × Nat) (s : State) : Prop :=
  PairStepStart p s ∧ s.z = !pairAny (Spec.Rsa.os2ip p.1.bytes) p.2

theorem pairStep_ct : RelCT isa (Two PairStepStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep (fun _ _ => True) := by
  have guardTrace : RelCT isa (Two PairStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (fun _ _ => True) :=
    (stackOnly_ct _ rfl).mono (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)
  have guard : RelCT isa (Two PairStepStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish) (Two PairGuarded) := by
    refine two_post guardTrace ?_
    intro p s h
    refine WP.mono (sieveFinish_ok h.trials.context.read.frame.space h.bad) ?_
    rintro t ⟨⟨flag,memory⟩,rest⟩
    refine ⟨⟨⟨h.trials.context.after_memory memory rest,h.trials.index,?_,?_⟩,?_⟩,flag⟩
    · rw [rest.gpr .r10 (by simp)]; exact h.trials.cursor
    · rw [memory]; exact h.trials.bytes
    · rw [memory,rest.sp]; exact h.bad
  refine guard.seq (two_ite ?_ ?_ ?_)
  · intro p s t h k
    change some s.z=some t.z
    rw [h.2,k.2]
  · exact pairActiveStep_ct.mono
      (fun _ _ ⟨p,a,b,sp⟩ => ⟨p,a.1.1.trials,b.1.1.trials,sp⟩) (fun _ _ h => h)
  · exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveSkip rfl).mono
      (fun _ _ ⟨_,_,_,sp⟩ => sp) (fun _ _ _ => trivial)

end VG.Proof.Ffdh.Arm.ParameterCandidate
