module

public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingBranch
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTimingInput
public import VerifiedGarbage.Impl.RsaKeyGen.X86.Candidate
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestTiming

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateFilterTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateExponentInput
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateDrawn
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateTestInput
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidatePreparedResult
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateResultTiming
import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.RsaKeyGen.CandLeak
import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateLoadInput
import VerifiedGarbage.Proof.MillerRabin.Contract
/-! # Publicly released coprimality decisions select equally timed candidate continuations -/

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidateIterationLeak.lean`, which only this module imported.
section

/-! # The released primality-result shape determines iterations and the final status -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont VG.Proof.RsaKeyGen

theorem iterations_eq {E : Environment} (v : E.Valid) {rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    (E.parameters rBytes).iterations = (E.parameters sBytes).iterations := by
  rw [MillerRabinLoop.Parameters.iterations, MillerRabinLoop.Parameters.iterations, v.test_eq, v.test_eq]
  change itersOf (8 * E.width) rBytes.length
      (shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop (8 * E.width)))) (8 * E.width) - 1 =
    itersOf (8 * E.width) sBytes.length
      (shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop (8 * E.width)))) (8 * E.width) - 1
  rw [v.length_eq, length, shape]

theorem result_status_eq {E : Environment} (v : E.Valid) {rBytes sBytes : List Byte} {s t : State}
    (left : MillerRabinLoop.Result (E.parameters rBytes) s)
    (right : MillerRabinLoop.Result (E.parameters sBytes) t)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    s.mem.readW (off E.base 168) 32 = t.mem.readW (off E.base 168) 32 := by
  apply BitVec.eq_of_toNat_eq
  rw [MillerRabinLoop.Result, v.test_eq] at left
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop (8 * E.width)) with
    | none => w32 s.mem E.base 168 = 0
    | some (prime, rest) => w32 s.mem E.base 168 = (if prime then 1 else 3) ∧
      w32 s.mem E.base 152 = rBytes.length - rest.length) at left
  rw [MillerRabinLoop.Result, v.test_eq] at right
  change (match Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop (8 * E.width)) with
    | none => w32 t.mem E.base 168 = 0
    | some (prime, rest) => w32 t.mem E.base 168 = (if prime then 1 else 3) ∧
      w32 t.mem E.base 152 = sBytes.length - rest.length) at right
  rw [v.length_eq] at left right
  cases a : Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length) with
  | none =>
    cases b : Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length) with
    | none => rw [a] at left; rw [b] at right; exact left.trans right.symm
    | some pr => simp only [a, b, shapeOf, Option.map_none, Option.map_some, reduceCtorEq] at shape
  | some pr =>
    obtain ⟨prime, rest⟩ := pr
    cases b : Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length) with
    | none => simp only [a, b, shapeOf, Option.map_none, Option.map_some, reduceCtorEq] at shape
    | some other =>
      obtain ⟨other, remaining⟩ := other
      have equal : prime = other := by
        simp only [a, b, shapeOf, Option.map_some, Option.some.injEq, Prod.mk.injEq] at shape
        exact shape.1
      rw [a] at left
      rw [b] at right
      exact left.1.trans (by rw [equal]; exact right.1.symm)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

-- Formerly `VerifiedGarbage/Proof/RsaKeyGen/X86/CandidatePreparedTiming.lean`, which only this module imported.
section

/-! # Complete prepared testing and export release only the declared primality shape -/

section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.RsaKeyGen VG.Proof.MillerRabin.X86 VG.Proof.Dsa.X86

theorem test_status_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFrame.code
        (VG.Impl.RsaKeyGen.X86.Candidate.testBody montName mont roundName round))
      (StatusPair E (candidateValue E rBytes) (candidateValue E sBytes)) := by
  intro s t tr ur u z H A B
  have trace := (test_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v
    (iterations_eq v length shape) enough _ _ _ _ _ _ H A B).1
  obtain ⟨VU, RU, WU, FU, KU⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.left H.savedLeft enough) A
  obtain ⟨VZ, RZ, WZ, FZ, KZ⟩ := wp_result (test_ok montVerified montNoSp montStack roundVerified roundNoSp roundStack
    v H.right H.savedRight enough) B
  refine ⟨trace, ⟨H.left.finishReady_after_test v VU WU FU KU, H.right.finishReady_after_test v VZ WZ FZ KZ, ?_⟩,
    result_status_eq v RU RZ shape⟩
  rw [KU.1 .esp (by unfold WitnessStep.clob; decide), KZ.1 .esp (by unfold WitnessStep.clob; decide),
    H.left.input.stack, H.right.input.stack]

theorem prepared_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.tested
  rw [mrResult_zero E.width]
  exact RelCT.seq (test_status_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough shape)
    (result_trace v)

end VG.Proof.RsaKeyGen.X86.Candidate
end

end

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Candidate
open VG VG.X86 VG.Proof.Mont.X86 VG.Proof.Dsa.X86 VG.Proof.RsaKeyGen

theorem drawn_used_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte} (status : Nat) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.CandidateFinish.used status) (fun _ _ => True) := by
  exact (CandidateFinish.used_trace (base := E.base) (size := E.size)
    (by have H : 256 ≤ E.size := v.geometry.headerFit; omega) status).mono (fun _ _ P =>
      ⟨P.left.input.scratch, P.right.input.scratch, P.left.input.usedPointer.trans P.right.input.usedPointer.symm⟩) (fun _ _ _ => trivial)

theorem exponent_pair_trace {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1)) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      VG.Impl.RsaKeyGen.X86.ExponentRt.code
      (WithFlag (TestPair E eBytes pBytes qBytes rBytes sBytes)
        (decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))) := by
  intro s t tr ur u z P A B
  have trace := (exponent_trace v _ _ _ _ _ _ P A B).1
  obtain ⟨DU, flagU, saveU, _, _⟩ := wp_result (exponent_ok v P.left) A
  obtain ⟨DZ, flagZ, saveZ, _, _⟩ := wp_result (exponent_ok v P.right) B
  exact ⟨trace, ⟨⟨DU, DZ⟩, saveU, saveZ⟩, flagU, by rw [same]; exact flagZ⟩

theorem TestPair.keepMem {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    {s t u z : State} (P : TestPair E eBytes pBytes qBytes rBytes sBytes s t) (MU : u.mem = s.mem) (MZ : z.mem = t.mem)
    {regs : List Reg} (KU : Keeps regs s u) (KZ : Keeps regs t z) (base : .edi ∉ regs) (sp : .esp ∉ regs)
    (SU : u.syms = s.syms) (SZ : z.syms = t.syms) : TestPair E eBytes pBytes qBytes rBytes sBytes u z := by
  refine ⟨⟨P.left.keepMem v MU KU base sp SU, P.right.keepMem v MZ KZ base sp SZ⟩, ?_, ?_⟩
  · rw [MU]; exact P.savedLeft
  · rw [MZ]; exact P.savedRight

theorem tested_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (shape : shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (TestPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.tested montName mont roundName round) (fun _ _ => True) := by
  exact prepared_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough shape

theorem exponent_stage_trace {mont round : Prog isa} {montName roundName : String}
    (montVerified : Verified target mont (Proof.Rsa.Mont.mulContract abi 56))
    (montNoSp : NoSp mont) (montStack : stackUse mont ≤ 56)
    (roundVerified : Verified target round (Proof.MillerRabin.Round.roundContract abi Proof.MillerRabin.Round.compact 96))
    (roundNoSp : NoSp round) (roundStack : stackUse round ≤ 96)
    {E : Environment} (v : E.Valid) {eBytes pBytes qBytes rBytes sBytes : List Byte}
    (length : rBytes.length = sBytes.length) (enough : E.length ≤ E.randLength)
    (same : decide (Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1) =
      decide (Nat.gcd (candidateValue E sBytes - 1) (Spec.Rsa.os2ip eBytes) = 1))
    (shape : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1 →
      shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E rBytes) (rBytes.drop E.length)) =
        shapeOf (Spec.RsaKeyGen.primalityTest (candidateValue E sBytes) (sBytes.drop E.length))) :
    RelCT isa (DrawnPair E eBytes pBytes qBytes rBytes sBytes)
      (VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck montName mont roundName round) (fun _ _ => True) := by
  unfold VG.Impl.RsaKeyGen.X86.Candidate.exponentCheck
  by_cases good : Nat.gcd (candidateValue E rBytes - 1) (Spec.Rsa.os2ip eBytes) = 1
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_true good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace true (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_false (tested_trace montVerified montNoSp montStack roundVerified roundNoSp roundStack v length enough
      (shape good))
  · have initialTrace := exponent_pair_trace (pBytes := pBytes) (qBytes := qBytes) v same
    rw [decide_eq_false good] at initialTrace
    refine RelCT.seq initialTrace (RelCT.seq ((cmp_flag_trace false (fun _ _ _ _ P U Z => P.keepFlags v U Z)).mono
      (fun _ _ P => P) (fun _ _ P => P.1)) ?_)
    exact branch_true ((drawn_used_trace v 3).mono (fun _ _ P => P.toDrawnPair) (fun _ _ _ => trivial))

end VG.Proof.RsaKeyGen.X86.Candidate
