module

public import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
public import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateHalve
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTSieveStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveMath
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SieveInit
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSieveMath
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedTests
/-! Halve p, screen q, then enter native rounds only when its public sieve passes. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTSieveLoop.lean`, which only this module imported.
section

/-! The RSA sieve loop has a public trace, including its public rejection flags. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTSieve.lean`, which only this module imported.
section

/-! Complete small-prime screening leaks only the public candidate and workspace layout. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def SievePublic (p : SieveData) (s : State) : Prop :=
  SieveContext p.dst p.base p.bytes.length s ∧ Spec.Rsa.bytesAt s.mem (State.addr p.dst) p.bytes.length = p.bytes

private theorem sieveInit_ct : RelCT isa (fun s t => s.sp = t.sp)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit (fun s t => s.sp = t.sp) := by
  have tail : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail)
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitRegisters (by decide)).seq (save_ct .r1 64))
  exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer (by decide)).seq tail

theorem sieve_ct : RelCT isa (Two SievePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (fun _ _ => True) := by
  have init : RelCT isa (Two SievePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit
      (Two fun p s => SieveCTState (p, 0) s) :=
    two_post (sieveInit_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (sieveInit_ok h.1) ?_
      intro t inv
      rw [h.2] at inv
      exact ⟨s, inv⟩)
  have finish : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish)
      (fun _ _ => True) := (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact init.seq ((relCT_keep_sp sieveLoop_ct (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (finish.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateSieve.lean`, which only this module imported.
section

/-! Reuse the native RSA sieve timing proof for either public candidate modulus. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure CandidateSieveStart (q : Bool) (p : CandidatePoint) (s : State) : Prop where
  context : CandidateContext p.params p.used s
  table : TableData p.params.base p.params.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = (candidatePhase p.params q).modulus
  odd : (candidatePhase p.params q).modulus % 2 = 1

structure CandidateSieved (q : Bool) (p : CandidatePoint) (s : State) : Prop where
  start : CandidateSieveStart q p s
  zero : s.z = (Spec.Ffdh.primeShape (candidatePhase p.params q).modulus &&
    !Spec.RsaKeyGen.obviouslyComposite p.params.bits (candidatePhase p.params q).modulus)

theorem candidateSieved_ok (q : Bool) (p : CandidatePoint) (s : State) (h : CandidateSieveStart q p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.sieve s (CandidateSieved q p) := by
  have large : 8161 < (candidatePhase p.params q).modulus := by
    cases q
    · exact p.params.sieve_large.1
    · exact p.params.sieve_large.2
  refine WP.mono (candidateSieve_ok h.context h.table (by rw [h.number]; exact large) (by rw [h.number]; exact h.odd)) ?_
  rintro t ⟨ctx, table, zero, bytes, _, _⟩
  rw [h.number] at zero
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.odd⟩, zero⟩

theorem candidateSieve_ct (q : Bool) : RelCT isa (Two (CandidateSieveStart q))
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (Two (CandidateSieved q)) := by
  refine two_post ?_ (candidateSieved_ok q)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length
  have length : xs.length = p.params.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.params.out) p.params.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have leftPublic : SievePublic ⟨p.params.out, p.params.base, xs⟩ s := by
    change SieveContext p.params.out p.params.base xs.length s ∧ _
    rw [length]
    exact ⟨left.context.sieve_context left.table, rfl⟩
  have rightPublic : SievePublic ⟨p.params.out, p.params.base, xs⟩ t := by
    change SieveContext p.params.out p.params.base xs.length t ∧ _
    rw [length]
    exact ⟨right.context.sieve_context right.table, same⟩
  exact sieve_ct _ _ _ _ _ _ ⟨_, leftPublic, rightPublic, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateTests.lean`, which only this module imported.
section

/-! The screened native controller depends only on the same public candidate and entropy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestsStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateTestStart true p s ∧ p.params.length ≤ p.params.bytes.length

theorem candidateTests_ct (v : RoundImpl) : RelCT isa (Two CandidateTestsStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code) (fun _ _ => True) :=
  (screenedTests_ct v).mono
    (fun _ _ h => two_mono (fun _ _ h => ⟨h.1.1, h.2, h.1.2.2⟩) h) (fun _ _ h => h)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenQStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  table : TableData p.base p.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private structure QHalved (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  table : TableData p.base p.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = (p.candidate - 1) / 2
  zero : s.z = decide (((p.candidate - 1) / 2) % 2 = 0)

private theorem qHalved_ok (p : CandidateParams) (s : State) (h : ScreenQStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ s (QHalved p) := by
  refine WP.mono (candidateHalve_ok h.context h.table h.number) ?_
  rintro t ⟨ctx, table, number, zero, _, _⟩
  exact ⟨ctx, h.enough, table, number, zero⟩

private def QSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidateSieveStart true ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def QSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidateSieved true ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem qSieve_ct (v : RoundImpl) : RelCT isa (Two QSieveStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.sieve,
      .ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected]) (fun _ _ => True) := by
  have sieve : RelCT isa (Two QSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.sieve (Two QSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidateSieve_ct true)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidateSieved_ok true _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two QSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint))
        (fun _ _ h => ⟨⟨h.1.1.start.context, h.1.1.start.number, h.1.1.start.odd⟩, h.1.2⟩) (candidateTests_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint))
        (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

theorem candidateScreenQ_ct (v : RoundImpl) : RelCT isa (Two ScreenQStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenQ v.name v.code) (fun _ _ => True) := by
  have halve : RelCT isa (Two ScreenQStart) VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ (Two QHalved) :=
    two_post (two_map (fun p => (p.out, p.length)) (fun _ _ h => h.context.read_context) halveQ_ct) qHalved_ok
  have branch : RelCT isa (Two QHalved)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected
        (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.sieve,
          .ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
            VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected])) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.context) candidateRejected_ct
    · refine two_map id ?_ (qSieve_ct v)
      intro p s h
      have odd : ((p.candidate - 1) / 2) % 2 = 1 := by
        have notEven : ¬ ((p.candidate - 1) / 2) % 2 = 0 := by
          have go := h.2
          change some s.z = some false at go
          rw [h.1.zero] at go
          exact of_decide_eq_false (Option.some.inj go)
        omega
      exact ⟨⟨h.1.context, h.1.table, h.1.number, odd⟩, h.1.enough⟩
  exact halve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
