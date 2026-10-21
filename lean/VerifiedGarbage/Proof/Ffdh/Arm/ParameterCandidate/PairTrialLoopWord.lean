module

public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TrialLoopWord
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairTrialWord
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Omega

/-! Simultaneous p and p-1 trial division through the shared RSA reducer. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.X25519.Arm
open VG.Impl.Ffdh.Arm.ParameterCandidate

theorem trialPairLoopWord_ok (s : State) {n : Nat} (positive : 0<n) (fits : n<2^32)
    (count : s.gpr .r1=BitVec.ofNat 32 n) (readable : TrialReadable s (s.gpr .r0) n) :
    WP isa (.loop trialPairStep .ne) s fun t =>
      t.gpr .r2=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) ∧
      t.gpr .r8=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8) ∧
      t.mem=s.mem ∧ Rest [.r0,.r1,.r2,.r5,.r6,.r7,.r8] s t := by
  induction n using Nat.strongRecOn generalizing s with
  | ind n ih =>
    obtain ⟨tr,u,run,valA,valB,ptr,cnt,flag,memory,rest⟩ :=
      trialPairStepWord_ok s positive fits count (readable.low positive) (fun h => readable.high h)
    have recurrenceA : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2)=
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n-min 2 n) (u.gpr .r2) := by
      rw [trialWordResult,dite_eq_right (by omega)]
      rw [memory,ptr,valA,rest.gpr .r3 (by simp),rest.gpr .r4 (by simp)]
    have recurrenceB : trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8)=
        trialWordResult u.mem (u.gpr .r0) (u.gpr .r3) (u.gpr .r4) (n-min 2 n) (u.gpr .r8) := by
      rw [trialWordResult,dite_eq_right (by omega)]
      rw [memory,ptr,valB,rest.gpr .r3 (by simp),rest.gpr .r4 (by simp)]
    by_cases last : n≤2
    · have zero : n-min 2 n=0 := by omega
      have resultA : u.gpr .r2=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r2) := by
        rw [recurrenceA,zero,trialWordResult,dite_eq_left rfl]
      have resultB : u.gpr .r8=trialWordResult s.mem (s.gpr .r0) (s.gpr .r3) (s.gpr .r4) n (s.gpr .r8) := by
        rw [recurrenceB,zero,trialWordResult,dite_eq_left rfl]
      exact ⟨_,u,.loopExit run (by change some (!u.z)=some false;rw [flag,decide_eq_true last];rfl),
        resultA,resultB,memory,rest⟩
    · have smaller : n-min 2 n<n := by omega
      have readU : TrialReadable u (u.gpr .r0) (n-min 2 n) := by
        rw [ptr]
        exact readable.advance rest (Nat.min_le_right 2 n)
      obtain ⟨trT,t,runT,resultA,resultB,memoryT,restT⟩ := ih _ smaller u (by omega) (by omega) cnt readU
      exact ⟨_,t,.loopNext run (by change some (!u.z)=some true;rw [flag,decide_eq_false last];rfl) runT,
        resultA.trans recurrenceA.symm,resultB.trans recurrenceB.symm,memoryT.trans memory,rest.trans restT⟩


end VG.Proof.Ffdh.Arm.ParameterCandidate
