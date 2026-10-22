module

import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateSchedule
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinTiming
public import VerifiedGarbage.Proof.RsaKeyGen.X86.MillerRabinOutcome
public import VerifiedGarbage.Proof.RsaKeyGen.X86.CandidateParameters

/-! # The released primality-result shape determines iterations and the final status -/

@[expose] public section
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
