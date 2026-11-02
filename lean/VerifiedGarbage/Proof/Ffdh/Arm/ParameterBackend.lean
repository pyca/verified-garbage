module

public import VerifiedGarbage.Proof.MillerRabin.Arm.Backend
public import VerifiedGarbage.Spec.Ffdh.Contract
public import VerifiedGarbage.Proof.Ffdh.Contract
public import VerifiedGarbage.Impl.Ffdh.Arm.ParameterCandidate
public import VerifiedGarbage.Spec.Ffdh.SievedContract

import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntered
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Spec.Ffdh.SievedCandidate
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateInput
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateDimensions
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Proof.Framework.Arm.Exec
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResiduePrime
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTResidueLow
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.ResidueLow
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Residue
import VerifiedGarbage.Proof.Bignum.Arm.StackOnlyCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTTrialBuffers
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateBuffers
import VerifiedGarbage.Proof.Bignum.OctetsValue
import VerifiedGarbage.Proof.Bignum.Octets
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateResult
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateShape
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateResidue
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateTest
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTCandidateFinish
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateCount
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTStackBlocks
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateMemory
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Room
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTLocal
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateStart
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.EntryContext
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateEntry
import VerifiedGarbage.Proof.Ffdh.Arm.KeySearch.CTBase
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateParams
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateFn
import VerifiedGarbage.Proof.Ffdh.Arm.FrameCT
import VerifiedGarbage.Proof.Framework.Sig
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateSat
import VerifiedGarbage.Proof.Ffdh.Arm.CallerRows
import VerifiedGarbage.Proof.Framework.Arm.CallF
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.TablePointer
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPieces
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairState
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairStep
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairMath
import VerifiedGarbage.Proof.Framework.Arm.Inline
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.SievePolicy
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTPairTrials
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.PairInit
import VerifiedGarbage.Proof.Bignum.Arm.StackCT
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.Table
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePair
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateTable
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidatePairMath
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTScreenedTests
import VerifiedGarbage.Proof.Bignum.Arm.PcDimensions
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CandidateQOdd
import VerifiedGarbage.Proof.Ffdh.Arm.ParameterCandidate.CTQOdd
/-! A verified parameter candidate supplied to the native retry/refill controller. -/

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTTable.lean`, which only this module imported.
section

/-! The native RSA sieve table is written at the same public scratch offsets in both runs. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_taint)

def TableStart (p : CandidateParams × Nat) (s : State) : Prop := CandidateContext p.1 p.2 s
private def TablePointer (p : CandidateParams × Nat) (s : State) : Prop :=
  s.gpr .r11 = p.1.base + BitVec.ofNat 32 (Proof.Rsa.Mont.arrAt p.1.words 34)

theorem tableWrite_ct : RelCT isa (Two TableStart)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) (fun _ _ => True) := by
  have pointer : RelCT isa (Two TableStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer) (Two TablePointer) :=
    two_post ((stackOnly_ct _ (by decide)).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (tablePointer_ok s p.1.base p.1.length p.1.length_bounds.2
        (by simpa only [BitVec.add_zero] using h.saved.read (d := 0) (by decide)) (h.saved.read (by decide))
        (by simpa only [BitVec.add_zero, candidateValues] using h.saved.saved 0 (by decide)) (h.saved.saved 12 (by decide))) ?_
      rintro t ⟨⟨ptr, _⟩, _⟩
      exact ptr)
  obtain ⟨hint, checked⟩ := tableWrites_taint
  have writes : RelCT isa (Two TablePointer) (.block (VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrites 1024))
      (fun _ _ => True) := by
    refine two_taint [.r11] ?_ checked
    intro p s t a b r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact a.trans b.symm
  exact RelCT.block_append (pointer.seq writes)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTPairLoop.lean`, which only this module imported.
section

/-! The RSA sieve loop has a public trace, including its public rejection flags. -/

section
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
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTPairSieve.lean`, which only this module imported.
section

/-! Complete small-prime screening leaks only the public candidate and workspace layout. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post)

def PairPublic (p : PairData) (s : State) : Prop :=
  SieveContext p.dst p.base p.bytes.length s ∧ Spec.Rsa.bytesAt s.mem (State.addr p.dst) p.bytes.length = p.bytes

private theorem sieveInit_ct : RelCT isa (fun s t => s.sp = t.sp)
    VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit (fun s t => s.sp = t.sp) := by
  have tail : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitTail)
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInitRegisters (by decide)).seq (save_ct .r1 64))
  exact (stackOnly_ct VG.Impl.Ffdh.Arm.ParameterCandidate.tablePointer (by decide)).seq tail

theorem pairSieve_ct : RelCT isa (Two PairPublic) VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (fun _ _ => True) := by
  have init : RelCT isa (Two PairPublic) VG.Impl.Ffdh.Arm.ParameterCandidate.sieveInit
      (Two fun p s => PairCTState (p, 0) s) :=
    two_post (sieveInit_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (pairInit_ok h.1) ?_
      intro t inv
      rw [h.2] at inv
      exact ⟨s, inv⟩)
  have finish : RelCT isa (fun s t => s.sp = t.sp) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.sieveFinish)
      (fun _ _ => True) := (stackOnly_ct _ rfl).mono (fun _ _ h => h) (fun _ _ _ => trivial)
  exact init.seq ((relCT_keep_sp pairLoop_ct (fun _ _ ⟨_, _, _, sp⟩ => sp)).seq
    (finish.seq (RelCT.block_nil (fun _ _ h => h))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidatePair.lean`, which only this module imported.
section

/-! Reuse the paired sieve timing proof without allocating a separate q buffer. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch

structure CandidatePairStart (p : CandidatePoint) (s : State) : Prop where
  context : CandidateContext p.params p.used s
  table : TableData p.params.base p.params.length s.mem
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length) = p.params.candidate
  oddQ : ((p.params.candidate-1)/2)%2=1

structure CandidatePaired (p : CandidatePoint) (s : State) : Prop where
  start : CandidatePairStart p s
  zero : s.z=candidateShapes p.params

theorem candidatePaired_ok (p : CandidatePoint) (s : State) (h : CandidatePairStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve s (CandidatePaired p) := by
  refine WP.mono (candidatePair_ok h.context h.table h.number h.oddQ) ?_
  rintro t ⟨ctx, table, zero, bytes, _, _⟩
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, zero⟩

theorem candidatePair_ct : RelCT isa (Two (CandidatePairStart))
    VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two (CandidatePaired)) := by
  refine two_post ?_ (candidatePaired_ok)
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.params.out) p.params.length
  have length : xs.length = p.params.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.params.out) p.params.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have leftPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ s := by
    change SieveContext p.params.out p.params.base xs.length s ∧ _
    rw [length]
    exact ⟨left.context.sieve_context left.table, rfl⟩
  have rightPublic : PairPublic ⟨p.params.out, p.params.base, xs⟩ t := by
    change SieveContext p.params.out p.params.base xs.length t ∧ _
    rw [length]
    exact ⟨right.context.sieve_context right.table, same⟩
  exact pairSieve_ct _ _ _ _ _ _ ⟨_, leftPublic, rightPublic, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateScreenPair.lean`, which only this module imported.
section

/-! The paired screening stage depends only on public candidate data. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPairStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length ≤ p.bytes.length
  oddQ : ((p.candidate-1)/2)%2=1
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length) = p.candidate

private def PSieveStart (p : CandidateParams) (s : State) : Prop :=
  CandidatePairStart ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private def PSieveEnd (p : CandidateParams) (s : State) : Prop :=
  CandidatePaired ⟨p, p.length⟩ s ∧ p.length ≤ p.bytes.length

private theorem pTable_ok (p : CandidateParams) (s : State) (h : ScreenPairStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite) s (PSieveStart p) := by
  refine WP.mono (candidateTable_ok h.context) ?_
  rintro t ⟨ctx, table, changed, _⟩
  have bytes := rsa_bytes_frame (src := State.addr p.out) (k := p.length) changed (by have := p.length_bounds; omega) (by
    intro r hr
    rw [List.mem_singleton] at hr
    subst r
    exact p.outputScratch)
  exact ⟨⟨ctx, table, by rw [bytes]; exact h.number, h.oddQ⟩, h.enough⟩

theorem candidateScreenPair_ct (v : RoundImpl) : RelCT isa (Two ScreenPairStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code) (fun _ _ => True) := by
  have table : RelCT isa (Two ScreenPairStart) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.tableWrite)
      (Two PSieveStart) :=
    two_post (two_map (fun p => (p, p.length)) (fun _ _ h => h.context) tableWrite_ct) pTable_ok
  have sieve : RelCT isa (Two PSieveStart) VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve (Two PSieveEnd) :=
    two_post ((two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1)
      (candidatePair_ct)).mono (fun _ _ h => h) (fun _ _ _ => trivial))
      (fun _ _ h => WP.mono (candidatePaired_ok _ _ h.1) (fun _ post => ⟨post, h.2⟩))
  have branch : RelCT isa (Two PSieveEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.tests v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.1.zero, right.1.zero]
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => ⟨h.1.1.start.context,h.1.2,h.1.1.start.oddQ⟩) (screenedTests_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.1.start.context) candidateRejected_ct
  exact table.seq (sieve.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateScreenP.lean`, which only this module imported.
section

/-! Reject even q before the paired RSA trial sieve and shared witness controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure ScreenPStart (p : CandidateParams) (s : State) : Prop where
  context : CandidateContext p p.length s
  enough : p.length≤p.bytes.length
  number : Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length)=p.candidate

private structure QOddChecked (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z=decide (((p.candidate-1)/2)%2=1)

private theorem qOdd_checked (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) s (QOddChecked p) := by
  refine WP.mono (candidateQOdd_ok h.context h.number) ?_
  rintro t ⟨ctx,zero,memory,_⟩
  exact ⟨⟨ctx,h.enough,by rw [memory]; exact h.number⟩,zero⟩

theorem candidateScreenP_ct (v : RoundImpl) : RelCT isa (Two ScreenPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code) (fun _ _ => True) := by
  have guard : RelCT isa (Two ScreenPStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.qOdd) (Two QOddChecked) :=
    two_post ((two_map (fun p => (p.out,p.length)) (fun _ _ h => h.context.read_context) qOdd_ct).mono
      (fun _ _ h => h) (fun _ _ _ => trivial)) qOdd_checked
  have branch : RelCT isa (Two QOddChecked)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite ?_ ?_ ?_
    · intro p s t a b
      change some s.z=some t.z
      rw [a.zero,b.zero]
    · refine two_map id ?_ (candidateScreenPair_ct v)
      intro p s h
      refine ⟨h.1.start.context,h.1.start.enough,?_,h.1.start.number⟩
      apply of_decide_eq_true
      have go : some s.z=some true := h.2
      exact h.1.zero.symm.trans (Option.some.inj go)
    · exact two_map (fun p => (⟨p,p.length⟩ : CandidatePoint))
        (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact guard.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidatePost.lean`, which only this module imported.
section

/-! Translate native status, output and entropy count to the public FFDH contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm

theorem candidatePost_spec {p : CandidateParams} {m : Mem} {r : BitVec 32} (post : candidatePost p m r) :
    let res := Spec.Ffdh.sievedParameterCandidate p.bits p.generator p.bytes
    r.toNat = Proof.Ffdh.candidateStatus res ∧
    Spec.Rsa.bytesAt m (State.addr p.out) p.length =
      (match res with | some (some n, _) => Spec.Rsa.i2osp n p.length | _ => List.replicate p.length 0) ∧
    Spec.Rsa.wordsAt m (State.addr p.usedPtr) 1 =
      [BitVec.ofNat 64 (match res with | some (_, tail) => p.bytes.length - tail.length | none => 0)] := by
  obtain ⟨status, count, bytes⟩ := post
  dsimp only
  rw [← candidateAnswer_spec p]
  cases answer : candidateAnswer p with
  | none =>
    rw [answer] at status count bytes
    exact ⟨by rw [status]; rfl, bytes, count⟩
  | some pair =>
    obtain ⟨pass, tail⟩ := pair
    rw [answer] at status count bytes
    cases pass <;> exact ⟨by rw [status]; rfl, bytes, count⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateCorrect.lean`, which only this module imported.
section

/-! The complete ARMv7 candidate callable satisfies the existing shared FFDH contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_correct (v : RoundImpl) (s : State)
    (pre : (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre s) :
    ∃ tr t, Exec isa (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) s tr t ∧
      abiPreserved s t ∧ (Proof.Ffdh.sievedParameterCandidateContract abi 184).post s t := by
  obtain ⟨p, args⟩ := candidatePublic s pre
  obtain ⟨tr, t, run, preserved, post⟩ := candidateFn_ok v (candidateInput pre args)
  refine ⟨tr, t, run, preserved, ?_⟩
  have result := candidatePost_spec post
  have widthNat : (s.gpr .r1).toNat = p.length := by
    rw [args.width, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.length_bounds; omega)]
  have bitsNat : (s.gpr .r3).toNat = p.bits := by
    rw [args.bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := p.maxBits; omega)]
  have generatorNat : (stackArg s 0).toNat = p.generator := by
    rw [args.generator, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rcases p.generatorAllowed with eq | eq <;> omega)]
  have tapeNat : (stackArg s 2).toNat = p.bytes.length := by
    rw [args.tapeLength, BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount]
  have bytes := args.bytes
  simp only [State.addr] at bytes result
  sig_post [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr]
  rw [BitVec.setWidth_append_eq_right]
  simp only [args.out, args.used, args.tape, widthNat, bitsNat, generatorNat, tapeNat, bytes]
  exact result

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTResidue2.lean`, which only this module imported.
section

/-! Generator-two filtering branches only on its public low candidate octet. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def Residue2Start (p : TrialData) (s : State) : Prop := TrialBuffers p s ∧ p.prime = 3#32

private def Residue2Low (p : TrialData) (s : State) : Prop := Residue2Start p s ∧
  s.z = decide ((p.values[0]?.getD 0).toNat % 8 = 3)

theorem residue2_ct : RelCT isa (Two Residue2Start) VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 (fun _ _ => True) := by
  have lowTrace : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow)
      (fun _ _ => True) :=
    two_map (fun p : TrialData => (p.dst, p.n)) (fun _ _ h => h.1.1) residueLow_ct
  have low : RelCT isa (Two Residue2Start) (.block VG.Impl.Ffdh.Arm.ParameterCandidate.residueLow) (Two Residue2Low) :=
    two_post lowTrace (fun p s h => by
      refine WP.mono (residueLow_ok s p.dst p.n (h.1.1.frame.read (by decide)) (h.1.1.frame.read (by decide))
        h.1.1.out h.1.1.width (h.1.1.readable.low h.1.1.positive)) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      have last : s.mem (State.addr (p.dst + BitVec.ofNat 32 p.n - 1)) = p.values[0]?.getD 0 := h.1.2 0 h.1.1.positive
      rw [last] at flag
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2⟩, flag⟩)
  have branch : RelCT isa (Two Residue2Low)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.residuePrime 3 [2, 5]) (.block [])) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · exact (residuePrime_ct 3 [2, 5] (by decide) residue2Equals_taint).mono
        (fun _ _ ⟨p, a, b, sp⟩ => ⟨p, a.1.1, b.1.1, sp⟩) (fun _ _ h => h)
    · exact RelCT.block_nil (fun _ _ _ => trivial)
  exact low.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTResidue.lean`, which only this module imported.
section

/-! Complete generator dispatch and congruence filtering depend only on public inputs. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two two_post two_map two_ite)

def ResiduePublic (p : TrialData × Nat) (s : State) : Prop :=
  TrialBuffers p.1 s ∧ (p.2 = 2 ∨ p.2 = 5) ∧
    s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.2

private def ResidueReady (p : TrialData × Nat) (s : State) : Prop :=
  ResiduePublic p s ∧ s.z = decide (p.2 = 2)

private def residueTrial (p : TrialData × Nat) (prime : BitVec 32) : TrialData := { p.1 with prime := prime }

theorem residue_ct : RelCT isa (Two ResiduePublic) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  have head : RelCT isa (Two ResiduePublic) (.block [.ldrSp .r1 28, .cmp .r1 (.imm 2)]) (Two ResidueReady) :=
    two_post ((stackOnly_ct _ rfl).mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) (fun p s h => by
      refine WP.mono (residueHead_ok h.1.1 (by rcases h.2.1 with eq | eq <;> omega) h.2.2) ?_
      rintro t ⟨⟨flag, memory⟩, rest⟩
      exact ⟨⟨⟨h.1.1.after_memory memory rest, by rw [memory]; exact h.1.2⟩, h.2.1,
        by rw [memory, rest.sp]; exact h.2.2⟩, flag⟩)
  have branch : RelCT isa (Two ResidueReady)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.residue2 VG.Impl.Ffdh.Arm.ParameterCandidate.residue5) (fun _ _ => True) := by
    refine two_ite (fun p s t a b => by change some s.z = some t.z; rw [a.2, b.2]) ?_ ?_
    · refine two_map (fun p => residueTrial p 3#32) ?_ residue2_ct
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
    · have five := residuePrime_ct 5 [2, 3, 7, 8] (by decide) residue5Equals_taint
      refine two_map (fun p => residueTrial p 5#32) ?_ five
      intro p s h
      exact ⟨h.1.1.1, rfl⟩
  exact head.seq branch

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateResidue.lean`, which only this module imported.
section

/-! Equal public candidate values give identical generator-residue traces. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)

theorem candidateResidue_ct : RelCT isa (Two ScreenPStart)
    VG.Impl.Ffdh.Arm.ParameterCandidate.residue (fun _ _ => True) := by
  intro s t trS trT u v h runS runT
  obtain ⟨p, left, right, sp⟩ := h
  let xs := Spec.Rsa.bytesAt s.mem (State.addr p.out) p.length
  have length : xs.length = p.length := VG.Proof.Bignum.bytesAt_length _ _ _
  have same : Spec.Rsa.bytesAt t.mem (State.addr p.out) p.length = xs :=
    VG.Proof.Bignum.bytesAt_eq_of_value length (right.number.trans left.number.symm)
  have buffersL := trialBuffers_of_octets (xs := xs) (prime := 0#32) left.context.read_context length rfl
  have buffersR := trialBuffers_of_octets (xs := xs) (prime := 0#32) right.context.read_context length same
  have genL : s.mem.readW (State.addr (s.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using left.context.saved.saved 28 (by simp [candidateSlots])
  have genR : t.mem.readW (State.addr (t.sp + 28#32)) 32 = BitVec.ofNat 32 p.generator := by
    simpa only [candidateValues] using right.context.saved.saved 28 (by simp [candidateSlots])
  exact residue_ct _ _ _ _ _ _ ⟨(⟨p.out, p.length, 0#32, xs.reverse⟩, p.generator), ⟨buffersL, p.generatorAllowed, genL⟩,
    ⟨buffersR, p.generatorAllowed, genR⟩, sp⟩ runS runT

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateTestP.lean`, which only this module imported.
section

/-! Restore and test p using the public original entropy prefix. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

def CandidateTestPStart (p : CandidatePoint) (s : State) : Prop :=
  CandidateContext p.params p.used s ∧ p.params.length ≤ p.params.bytes.length

theorem candidateTestP_ct (v : RoundImpl) : RelCT isa (Two CandidateTestPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP,
      VG.Impl.Ffdh.Arm.ParameterCandidate.test false v.name v.code, VG.Impl.Ffdh.Arm.ParameterCandidate.result])
    (fun _ _ => True) := by
  have shapeTrace : RelCT isa (Two CandidateTestPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.params.out, p.params.tape, p.params.bytes.take p.params.length, p.params.bits⟩ : ShapeData))
      (fun _ _ h => h.1.shape_context h.2) shapeP_ct
  have shape : RelCT isa (Two CandidateTestPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP
      (Two (CandidateTestStart false)) :=
    two_post shapeTrace (fun p _ h => WP.mono (candidateShape_ok h.1 h.2)
      (fun _ ⟨ctx, _, number, _, _⟩ => ⟨ctx, number, p.params.candidate_odd⟩))
  exact shape.seq ((candidateTestResult_ct v false).seq
    ((candidatePhaseResult_ct false).seq (RelCT.block_nil (fun _ _ _ => trivial))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateMain.lean`, which only this module imported.
section

/-! Complete native candidate controller timing from public entropy and buffer descriptors. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Bignum.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CountedStart (p : CandidateParams) (s : State) : Prop :=
  CandidateContext p p.length s ∧ p.length ≤ p.bytes.length

private structure CandidateResidueEnd (p : CandidateParams) (s : State) : Prop where
  start : ScreenPStart p s
  zero : s.z = Spec.Ffdh.generationShape p.bits p.generator p.candidate

private theorem candidateResidueEnd_ok (p : CandidateParams) (s : State) (h : ScreenPStart p s) :
    WP isa VG.Impl.Ffdh.Arm.ParameterCandidate.residue s (CandidateResidueEnd p) := by
  refine WP.mono (candidateResidue_ok h.context h.number) ?_
  rintro t ⟨ctx, zero, mem, _⟩
  exact ⟨⟨ctx, h.enough, by rw [mem]; exact h.number⟩, zero⟩

theorem candidateMain_ct (v : RoundImpl) : RelCT isa (Two CandidateTestPStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code) (fun _ _ => True) := by
  have countTrace : RelCT isa (fun s t => s.sp = t.sp)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40))
      (fun s t => s.sp = t.sp) :=
    RelCT.block_append ((stackOnly_ct [.ldrSp .r1 12] rfl).seq (save_ct .r1 40))
  have count : RelCT isa (Two CandidateTestPStart)
      (.block (([.ldrSp .r1 12] : List Instr) ++ VG.Impl.Ffdh.Arm.ParameterCandidate.save .r1 40)) (Two CountedStart) :=
    (two_post (countTrace.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial))
      (fun p _ h => WP.mono (candidateCount_ok h.1 h.2) (fun _ ⟨ctx, _, _⟩ => (show CountedStart p.params _ from ⟨ctx, h.2⟩)))).mono
      (fun _ _ h => h) (fun _ _ ⟨p, left, right, sp⟩ => ⟨p.params, left, right, sp⟩)
  have shapeTrace : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (fun _ _ => True) :=
    two_map (fun p => (⟨p.out, p.tape, p.bytes.take p.length, p.bits⟩ : ShapeData)) (fun _ _ h => h.1.shape_context h.2) shapeP_ct
  have shape : RelCT isa (Two CountedStart) VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP (Two ScreenPStart) :=
    two_post shapeTrace (fun _ _ h => WP.mono (candidateShape_ok h.1 h.2) (fun _ ⟨ctx, _, number, _, _⟩ => ⟨ctx, h.2, number⟩))
  have residue : RelCT isa (Two ScreenPStart) VG.Impl.Ffdh.Arm.ParameterCandidate.residue (Two CandidateResidueEnd) :=
    two_post candidateResidue_ct candidateResidueEnd_ok
  have branch : RelCT isa (Two CandidateResidueEnd)
      (.ite .eq (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP v.name v.code)
        VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected) (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.zero, right.zero]
    · exact two_map id (fun _ _ h => h.1.start) (candidateScreenP_ct v)
    · exact two_map (fun p => (⟨p, p.length⟩ : CandidatePoint)) (fun _ _ h => h.1.start.context) candidateRejected_ct
  exact count.seq (shape.seq (residue.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateGuard.lean`, which only this module imported.
section

/-! Short entropy returns and the full native candidate body share the public tape-length guard. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

private def CandidateRoomEnd (p : CandidatePoint) (s : State) : Prop :=
  CandidateContextStart p s ∧ s.z = decide (p.params.bytes.length < p.params.length)

private theorem candidateRoomEnd_ok (p : CandidatePoint) (s : State) (h : CandidateContextStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) s (CandidateRoomEnd p) := by
  refine WP.mono (initialRoom_ok h.saved.space p.params.tapeCount
    (by have := p.params.length_bounds; omega) (h.saved.saved 20 (by decide)) (h.saved.saved 12 (by decide))) ?_
  rintro t ⟨⟨zero, mem⟩, rest⟩
  exact ⟨h.after_memory mem rest, zero⟩

theorem candidateGuard_ct (v : RoundImpl) : RelCT isa (Two CandidateContextStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)])
    (fun _ _ => True) := by
  have room : RelCT isa (Two CandidateContextStart)
      (.block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom) (Two CandidateRoomEnd) :=
    two_post (initialRoom_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateRoomEnd_ok
  have branch : RelCT isa (Two CandidateRoomEnd)
      (.ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code))
      (fun _ _ => True) := by
    refine two_ite (fun _ _ _ left right => ?_) ?_ ?_
    · change some _ = some _
      rw [left.2, right.2]
    · exact two_map id (fun _ _ h => h.1.1) candidateNone_ct
    · refine two_map id ?_ (candidateMain_ct v)
      intro p s h
      have enough : p.params.length ≤ p.params.bytes.length := by
        have go := h.2
        change some s.z = some false at go
        rw [h.1.2] at go
        have := of_decide_eq_false (Option.some.inj go)
        omega
      exact ⟨h.1.1, enough⟩
  exact room.seq (branch.seq (RelCT.block_nil (fun _ _ _ => trivial)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTEntry.lean`, which only this module imported.
section

/-! The complete native candidate entry has a fixed stack-address trace. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm

private def entryStores : List (Reg × Nat) := [(.r0, 4), (.r0, 8), (.r1, 12), (.r2, 32), (.r3, 24)]
private def entryCopies : List (Nat × Nat) := [(128, 28), (132, 16), (136, 20), (140, 0), (144, 36)]

theorem candidateEntry_ct : RelCT isa (fun s t => s.sp = t.sp)
    (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) (fun s t => s.sp = t.sp) := by
  have zero : RelCT isa LocalAddress (.block [.mov .r0 (.imm 0), .str .r0 .r12 40]) LocalAddress :=
    RelCT.block_append (localZero_ct.seq (storeLocal_ct .r0 40))
  have tail : RelCT isa LocalAddress (.block
      ((entryStores.map fun p => Instr.str p.1 .r12 p.2) ++
        (entryCopies.flatMap fun p => [Instr.ldrSp .r0 p.1, Instr.str .r0 .r12 p.2]) ++
        [.mov .r0 (.imm 0), .str .r0 .r12 40])) LocalAddress :=
    RelCT.block_append ((RelCT.block_append ((localStores_ct entryStores).seq (localCopies_ct entryCopies))).seq zero)
  change RelCT isa _ (.block ([.addSp .r12 0] ++ _)) _
  exact RelCT.block_append (stackAddr_ct.seq (tail.mono (fun _ _ h => h) (fun _ _ h => h.2)))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateEntered.lean`, which only this module imported.
section

/-! Native entry snapshots the public candidate arguments before the complete controller. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.Ffdh.Arm.KeySearch
open VG.Proof.MillerRabin.Arm (RoundImpl)

structure CandidateEntryStart (p : CandidateParams) (s : State) : Prop where
  start : CandidateStart p s
  incoming : CandidateIncoming p s
  out : s.gpr .r0 = p.out
  width : s.gpr .r1 = BitVec.ofNat 32 p.length
  used : s.gpr .r2 = p.usedPtr
  bits : s.gpr .r3 = BitVec.ofNat 32 p.bits

private theorem candidateEntryStart_ok (p : CandidateParams) (s : State) (h : CandidateEntryStart p s) :
    WP isa (.block VG.Impl.Ffdh.Arm.ParameterCandidate.entry) s (CandidateContextStart ⟨p, 0⟩) := by
  refine WP.mono (candidateEntry_ok h.start.locals h.incoming h.out h.width h.used h.bits) ?_
  rintro t ⟨saved, changed, rest⟩
  exact h.start.after_entry saved changed rest

theorem candidateEntered_ct (v : RoundImpl) : RelCT isa (Two CandidateEntryStart)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.seqs [
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.entry,
      .block VG.Impl.Ffdh.Arm.ParameterCandidate.initialRoom,
      .ite .eq VG.Impl.Ffdh.Arm.ParameterCandidate.finNone (VG.Impl.Ffdh.Arm.ParameterCandidate.main v.name v.code)])
    (fun _ _ => True) :=
  (two_post (candidateEntry_ct.mono (fun _ _ ⟨_, _, _, sp⟩ => sp) (fun _ _ _ => trivial)) candidateEntryStart_ok).seq
    ((candidateGuard_ct v).mono (fun _ _ ⟨p, left, right, sp⟩ => ⟨⟨p, 0⟩, left, right, sp⟩) (fun _ _ h => h))

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CTCandidateFn.lean`, which only this module imported.
section

/-! The common AAPCS frame preserves the full candidate's public timing policy. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Proof.Ffdh.Arm
open VG.Proof.Ffdh.Arm.KeySearch (Two)
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidateFn_ct (v : RoundImpl) : RelCT isa (Two CandidateFnInput)
    (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) (fun _ _ => True) := by
  refine framed_ct (fun _ _ ⟨_, left, right, _⟩ => ⟨by have := left.stackFits; omega, by have := right.stackFits; omega⟩)
    (fun _ _ ⟨_, _, _, sp⟩ => sp) ?_
  refine (candidateEntered_ct v).mono ?_ (fun _ _ h => h)
  rintro a b ⟨s, t, ⟨p, left, right, sp⟩, rfl, rfl⟩
  exact ⟨p, ⟨left.start, left.incoming, left.out, left.width, left.used, left.bits⟩,
    ⟨right.start, right.incoming, right.out, right.width, right.used, right.bits⟩,
    by change s.sp - 56#32 - 72#32 = t.sp - 56#32 - 72#32; rw [sp]⟩

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/CandidateContractCT.lean`, which only this module imported.
section

/-! The native candidate satisfies the public shared FFDH timing contract. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_contract_ct (v : RoundImpl) : ConstantTime isa (Proof.Ffdh.sievedParameterCandidateContract abi 184).pre
    (Proof.Ffdh.sievedParameterCandidateContract abi 184).pub (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) := by
  intro s t trS trT u z hs ht hp runS runT
  obtain ⟨p, args⟩ := candidatePublic s hs
  sig_pub [Proof.Ffdh.sievedParameterCandidateContract, Proof.Ffdh.parameterCandidateSig,
    abi, argRegs, reduceClassify, Loc.val, State.addr] at hp
  obtain ⟨sp, bytes, p0, p1, p2, p3, p4, p5, p6, p7, p8⟩ := hp
  have byteEq := congrArg (List.map (BitVec.ofNat 8)) bytes
  simp only [List.map_map, Function.comp_def, BitVec.ofNat_toNat, BitVec.setWidth_eq, List.map_id'] at byteEq
  have argsT : CandidateAbi p t := {
    out := p0.symm.trans args.out
    width := p1.symm.trans args.width
    used := p2.symm.trans args.used
    bits := p3.symm.trans args.bits
    generator := p4.symm.trans args.generator
    tape := p5.symm.trans args.tape
    tapeLength := p6.symm.trans args.tapeLength
    base := p7.symm.trans args.base
    capacity := p8.symm.trans args.capacity
    bytes := by
      rw [← p5, ← p6, args.tape, args.tapeLength] at byteEq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt p.tapeCount] at byteEq
      exact byteEq.symm.trans args.bytes }
  exact ((candidateFn_ct v) _ _ _ _ _ _ ⟨p, candidateInput hs args, candidateInput ht argsT, sp⟩ runS runT).1

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Verified.lean`, which only this module imported.
section

/-! Complete native ARMv7 parameter candidates satisfy the shared public API. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

theorem candidate_verified (v : RoundImpl) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code)
      (Proof.Ffdh.sievedParameterCandidateContract abi 184) :=
  ⟨candidate_correct v, candidate_contract_ct v, candidate_sat⟩

theorem optimizedCandidate_verified (umaal : Bool) (v : RoundImpl) :
    Verified target (VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode umaal v.name v.code)
      (Proof.Ffdh.sievedParameterCandidateContract abi 184) := by
  cases umaal with
  | false => exact candidate_verified v
  | true => exact VG.Proof.Ffdh.Arm.CallerRows.verified (candidate_verified v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/StackPieces.lean`, which only this module imported.
section

/-! Fixed candidate operations do not allocate additional stack frames. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm VG.Impl.Ffdh.Arm.ParameterCandidate

theorem shapeP_stack : FrameStack.armStack shapeP = 0 := by decide +kernel
theorem residue_stack : FrameStack.armStack residue = 0 := by decide +kernel
theorem pairSieve_stack : FrameStack.armStack pairSieve = 0 := by decide +kernel
theorem sieve_stack : FrameStack.armStack sieve = 0 := by decide +kernel
theorem halveQ_stack : FrameStack.armStack halveQ = 0 := by decide +kernel
theorem finNone_stack : FrameStack.armStack finNone = 0 := by decide +kernel
theorem finRejected_stack : FrameStack.armStack finRejected = 0 := by decide +kernel
theorem result_stack : FrameStack.armStack result = 0 := by decide +kernel
theorem phasePrepared_stack : FrameStack.armStack phasePrepared = 0 := by decide +kernel
theorem drawRange_stack : FrameStack.armStack drawRange = 0 := by decide +kernel
theorem montEncode_stack : FrameStack.armStack (VG.Impl.Bignum.Arm.montOp 5 1 4) = 0 := by decide +kernel
theorem onPass_stack : FrameStack.armStack onPass = 0 := by decide +kernel

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

-- Formerly `VerifiedGarbage/Proof/Ffdh/Arm/ParameterCandidate/Stack.lean`, which only this module imported.
section

/-! The candidate frame and shared round require at most 184 bytes of stack. -/

section
namespace VG.Proof.Ffdh.Arm.ParameterCandidate
open VG VG.Arm
open VG.Proof.MillerRabin.Arm (RoundImpl)

private theorem candidate_code_stack (name : String) (body : Prog isa) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code name body) = FrameStack.armStack body + 128 := by
  have roundKernelStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Bignum.Arm.montOp 5 1 4)) (max 0 (max (FrameStack.armStack body) 0)) = _
    rw [montEncode_stack, Nat.max_zero, Nat.zero_max, Nat.zero_max]
  have roundStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.round name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.roundKernel name body)) (max 0 (max (max 0 (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.onPass)) 0)) = _
    rw [roundKernelStack, onPass_stack]
    simp only [Nat.max_self, Nat.max_zero]
  have drawStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.draw name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.drawRange) (max 0 (max (max 0 (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.round name body))) 0)) = _
    rw [drawRange_stack, roundStack]
    simp only [Nat.zero_max, Nat.max_zero]
  have stepStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep name body) = FrameStack.armStack body := by
    change max 0 (max (max 0 (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.draw name body))) 0) = _
    rw [drawStack]
    simp only [Nat.zero_max, Nat.max_zero]
  have testStack (q : Bool) : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.test q name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared)
      (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep name body))) = _
    rw [phasePrepared_stack, stepStack, Nat.zero_max, Nat.zero_max]
  have limitedStack (first : Bool) : FrameStack.armStack
      (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited first name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.phasePrepared)
      (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.witnessStep name body))) = _
    rw [phasePrepared_stack, stepStack, Nat.zero_max, Nat.zero_max]
  have finalStack : FrameStack.armStack
      (VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP)
      (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited false name body))
        (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.result) 0)) = _
    rw [shapeP_stack, limitedStack false, result_stack]
    simp only [Nat.zero_max, Nat.max_zero]
  have afterQStack : FrameStack.armStack
      (VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.test true name body))
      (max 0 (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.limitedFinal name body))
        (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.result)) 0)) = _
    rw [testStack true, finalStack, result_stack]
    simp only [Nat.zero_max, Nat.max_zero, Nat.max_self]
  have qStack : FrameStack.armStack
      (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.halveQ)
      (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.afterScreenedQ name body)) = _
    rw [halveQ_stack, afterQStack, Nat.zero_max]
  have testsStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.tests name body) = FrameStack.armStack body := by
    change max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP)
      (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.testLimited true name body))
        (max 0 (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenedQ name body))
          (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.result)) 0))) = _
    rw [shapeP_stack, limitedStack true, qStack, result_stack]
    simp only [Nat.zero_max, Nat.max_zero, Nat.max_self]
  have screenPairStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.pairSieve)
      (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.tests name body))
        (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0)) = _
    rw [pairSieve_stack,testsStack,finRejected_stack]
    simp only [Nat.zero_max,Nat.max_zero]
  have screenPStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP name body) = FrameStack.armStack body := by
    change max 0 (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenPair name body))
      (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0) = _
    rw [screenPairStack,finRejected_stack]
    simp only [Nat.zero_max,Nat.max_zero]
  have mainStack : FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.main name body) = FrameStack.armStack body := by
    change max 0 (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.shapeP)
      (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.residue)
        (max (max (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.screenP name body))
          (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finRejected)) 0))) = _
    rw [shapeP_stack, residue_stack, screenPStack, finRejected_stack]
    simp only [Nat.zero_max, Nat.max_zero]
  change max 0 (max 0 (max (max (FrameStack.armStack VG.Impl.Ffdh.Arm.ParameterCandidate.finNone)
    (FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.main name body))) 0)) + 72 + 56 = _
  rw [finNone_stack, mainStack]
  simp only [Nat.zero_max, Nat.max_zero, Nat.add_assoc]

theorem candidate_stack (v : RoundImpl) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.code v.name v.code) ≤ 184 := by
  rw [candidate_code_stack]
  have := v.stack
  omega

theorem optimizedCandidate_stack (umaal : Bool) (v : RoundImpl) :
    FrameStack.armStack (VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode umaal v.name v.code) ≤ 184 := by
  cases umaal with
  | false => exact candidate_stack v
  | true => exact (VG.Proof.Ffdh.Arm.CallerRows.stack _).trans (candidate_stack v)

end VG.Proof.Ffdh.Arm.ParameterCandidate
end

end

@[expose] public section
namespace VG.Proof.Ffdh.Arm
open VG VG.Arm

structure ParameterBackend where
  candidate : Prog isa
  candidate_verified : Verified target candidate (Proof.Ffdh.sievedParameterCandidateContract abi 184)
  candidateStack : FrameStack.armStack candidate ≤ 184
  suffix : String
  features : List String

def ParameterBackend.candidateName (b : ParameterBackend) : String :=
  "vg_ffdh_parameter_candidate_sieved" ++ b.suffix

def parameterBackend (v : VG.Proof.MillerRabin.Arm.RoundImpl) : ParameterBackend := by
  exact {
    candidate := VG.Impl.Ffdh.Arm.ParameterCandidate.optimizedCode (v.features.contains "umaal") v.name v.code
    candidate_verified := by exact ParameterCandidate.optimizedCandidate_verified _ v
    candidateStack := by exact ParameterCandidate.optimizedCandidate_stack _ v
    suffix := v.suffix
    features := v.features }

end VG.Proof.Ffdh.Arm
