module

public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSieveStep
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy

/-! The RSA sieve loop has a public trace, including its public rejection flags. -/

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG.Impl.Ffdh.Arm.ParameterCandidate (trialCount)
open VG VG.Arm VG.Proof.Bignum
open VG.Proof.Ffdh.Arm.KeySearch (Two)

def SieveCTState (p : SieveData × Nat) (s : State) : Prop :=
  ∃ original, SieveInv original p.1.dst p.1.base p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2 s

private theorem SieveCTState.step_start {p : SieveData × Nat} {s : State}
    (h : SieveCTState p s) (more : p.2 < (trialCount p.1.bytes.length)) : SieveStepStart p s := by
  obtain ⟨original, inv⟩ := h
  exact ⟨inv.context, more, inv.cursor, bytesAt_eq_of_value rfl inv.candidate, inv.bad⟩

private theorem sieveStep_fixed (p : SieveData × Nat) (more : p.2 < (trialCount p.1.bytes.length)) :
    RelCT isa (fun s t => SieveCTState p s ∧ SieveCTState p t ∧ s.sp = t.sp)
      VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep
      (fun s t => SieveCTState (p.1, (sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) s ∧ SieveCTState (p.1, (sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)) t ∧
        s.z = decide ((sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ t.z = decide ((sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)) ∧ s.sp = t.sp) := by
  intro s t trS trT u v h runS runT
  have leak := (sieveStep_ct _ _ _ _ _ _ ⟨p, h.1.step_start more, h.2.1.step_start more, h.2.2⟩ runS runT).1
  obtain ⟨originalS, invS⟩ := h.1
  obtain ⟨originalT, invT⟩ := h.2.1
  obtain ⟨_, u', execS, nextS, zeroS⟩ := sieveStep_ok invS more
  obtain ⟨_, v', execT, nextT, zeroT⟩ := sieveStep_ok invT more
  obtain ⟨_, rfl⟩ := Exec.det runS execS
  obtain ⟨_, rfl⟩ := Exec.det runT execT
  exact ⟨leak, ⟨originalS, nextS⟩, ⟨originalT, nextT⟩, zeroS, zeroT,
    (Exec.rdwr runS).2.2.trans (h.2.2.trans (Exec.rdwr runT).2.2.symm)⟩

private def SieveLoopPair (remaining : Nat) (s t : State) : Prop :=
  ∃ p : SieveData × Nat, p.2 < (trialCount p.1.bytes.length) ∧ (trialCount p.1.bytes.length) - p.2 ≤ remaining ∧ SieveCTState p s ∧ SieveCTState p t ∧ s.sp = t.sp

theorem sieveLoop_ct : RelCT isa (Two fun (p : SieveData) s => SieveCTState (p, 0) s)
    (.loop VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep .ne) (fun _ _ => True) := by
  have step : ∀ n, RelCT isa (SieveLoopPair n) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveStep
      (fun u v => isa.eval .ne u = isa.eval .ne v ∧
        (isa.eval .ne u = some false → True) ∧
        (isa.eval .ne u = some true → ∃ m, m < n ∧ SieveLoopPair m u v)) := by
    intro n s t trS trT u v h runS runT
    obtain ⟨p, more, remaining, left, right, sp⟩ := h
    have progress := sieveNext_progress (value:=Spec.Rsa.os2ip p.1.bytes) more
    obtain ⟨leak, stateU, stateV, zeroU, zeroV, spUV⟩ := sieveStep_fixed p more _ _ _ _ _ _ ⟨left, right, sp⟩ runS runT
    refine ⟨leak, ?_, by intro _; trivial, ?_⟩
    · change some (!u.z) = some (!v.z)
      rw [zeroU, zeroV]
    · intro go
      change some (!u.z) = some true at go
      have next : (sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) < (trialCount p.1.bytes.length) := by
        by_cases last : (sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2) = (trialCount p.1.bytes.length)
        · rw [zeroU, decide_eq_true last] at go
          cases go
        · omega
      exact ⟨(trialCount p.1.bytes.length) - ((sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), by omega, (p.1, (sieveNext p.1.bytes.length (Spec.Rsa.os2ip p.1.bytes) p.2)), next, by exact Nat.le_refl _, stateU, stateV, spUV⟩
  exact (RelCT.loop SieveLoopPair step 1024).mono
    (fun _ _ ⟨p, left, right, sp⟩ => ⟨(p, 0), trialCount_positive _, by change trialCount p.bytes.length - 0 ≤ 1024; have := trialCount_bound p.bytes.length; omega, left, right, sp⟩) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
