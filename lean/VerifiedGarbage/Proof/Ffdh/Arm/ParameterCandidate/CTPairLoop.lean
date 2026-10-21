module

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairStep
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairMath
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairTrials

/-! The RSA sieve loop has a public trace, including its public rejection flags. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Bignum
open VG.Proof.Ffdh.Arm.KeySearch (Two)

def PairCTState (p : PairData × Nat) (s : State) : Prop :=
  ∃ original, PairInv original p.1.dst p.1.base p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2 s

private theorem PairCTState.step_start {p : PairData × Nat} {s : State}
    (h : PairCTState p s) (more : p.2 < (trialCount p.1.bytes.length)) : PairStepStart p s := by
  obtain ⟨original, inv⟩ := h
  exact ⟨⟨inv.context, more, inv.cursor, bytesAt_eq_of_value rfl inv.candidate⟩, inv.bad⟩

private theorem pairStep_fixed (p : PairData × Nat) (more : p.2 < (trialCount p.1.bytes.length)) :
    RelCT isa (fun s t => PairCTState p s ∧ PairCTState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
      (fun s t => PairCTState (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) s ∧ PairCTState (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) t ∧
        s.z = decide ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ t.z = decide ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (pairStep_ct _ _ _ _ _ _ ⟨p, h.1.step_start more, h.2.1.step_start more, h.2.2⟩ runS runT).1
  obtain ⟨originalS, invS⟩ := h.1
  obtain ⟨originalT, invT⟩ := h.2.1
  obtain ⟨_, u', execS, nextS, zeroS⟩ := pairStep_ok invS more
  obtain ⟨_, v', execT, nextT, zeroT⟩ := pairStep_ok invT more
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, ⟨originalS, nextS⟩, ⟨originalT, nextT⟩, zeroS, zeroT,
    (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def PairLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : PairData × Nat, p.2 < (trialCount p.1.bytes.length) ∧ (trialCount p.1.bytes.length) - p.2 ≤ remaining ∧ PairCTState p s ∧ PairCTState p t ∧ s.sp = t.sp

theorem pairLoop_ct : RelCT isa (Two fun (p : PairData) s => PairCTState (p, 0) s)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep .ne) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (PairLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.pairStep
      (fun u v => isa.eval .ne u = isa.eval .ne v ∧
        (isa.eval .ne u = some false → True) ∧
        (isa.eval .ne u = some true → ∃ m, m < n ∧ PairLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, more, remaining, left, right, sp⟩ := h
    have progress := pairNext_progress (value:=Spec.Rsa.os2ip p.1.bytes) more
    obtain ⟨leak, stateU, stateV, zeroU, zeroV, spUV⟩ := pairStep_fixed p more _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zeroU, zeroV]
    · intro go
      change some (!u.z) = some true at go
      have next : (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) < (trialCount p.1.bytes.length) := by
        by_cases last : (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)
        · rw [zeroU, decide_eq_true last] at go
          cases go
        · omega
      exact ⟨(trialCount p.1.bytes.length) - ((pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), by omega, (p.1, (pairNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), next, by exact Nat.le_refl _, stateU, stateV, spUV⟩
  exact (RelCT.loop PairLoopPair step 1024).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨(p, 0), trialCount_positive _, by change trialCount p.bytes.length - 0 ≤ 1024; have := trialCount_bound p.bytes.length; omega, left, right, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
