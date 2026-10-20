module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimeRunSpec
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchStatus
import VerifiedGarbage.Proof.Dsa.X86.Generation.PAttempt
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchValue

/-! # A complete native attempt advances exactly one reviewed p-search step -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem pSearch_step {H : Hash} (K : HashOK H) {P : PSearchPlan}
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length)
    {expected : Option (Option Nat × List Byte)} {initial s : State} {counter : Nat}
    (bound : counter < 32 * P.context.geometry.pLen) (I : PSearchInvariant P expected initial counter s)
    (C : SearchControl (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter
      (P.context.geometry.contributionCount + 1) s) :
    WP isa (pAttempt H P.context.geometry.pLen P.context.geometry.qLen) s fun t =>
      SearchControl (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) counter
        (P.context.geometry.contributionCount + 1) t ∧
      ∃ status ≤ 3, t.mem.readW (off (off P.context.geometry.base VG.Impl.Dsa.Generation.Layout.control) 8) 32 = BitVec.ofNat 32 status ∧
        (if status = 3 then PSearchInvariant P expected initial (counter + 1) t else PSearchFinished P expected initial t) := by
  obtain ⟨W, used, R, cursor, usedBound, _, remaining, Oi, rd, wr⟩ := I
  have shape := P.value_shape counter hashSize
  refine WP.mono (pAttempt_ok K R.context R.seed P.seedLength digest final bound C R.source cursor usedBound
    R.qval P.qPositive P.qBound hash hashSize shape.1 shape.2)
    fun t ⟨Wt, result, Rt, source, seedCursorT, cursorT, statusT, seedT, qvalT, pb, eb, outcome, Ct, status, O, Kt⟩ => ?_
  have memory : PSearchMemory P Wt t := ⟨Rt, seedT, source, qvalT, seedCursorT.trans R.seedUsed⟩
  have total := Oi.trans O
  have rdt := Kt.2.1.trans rd
  have wrt := Kt.2.2.trans wr
  have limit : result.status ≤ 3 := by rcases outcome.status with h | h | h <;> omega
  refine ⟨Ct, result.status, limit, status, ?_⟩
  by_cases small : P.value counter < 2 ^ (8 * P.context.geometry.pLen - 1)
  · have spec := outcome.spec
    change (if P.value counter < _ then _ else _) at spec
    rw [ite_eq_left small] at spec
    rw [ite_eq_left spec.1]
    have next : expected = P.remaining (counter + 1) result.used := by
      rw [remaining, P.remaining_step bound, ite_eq_left small, spec.2]
    exact ⟨Wt, result.used, memory, cursorT, outcome.bound,
      fun _ => by rw [statusT, spec.1]; rfl, next, total, rdt, wrt⟩
  · have spec := outcome.spec
    change (if P.value counter < _ then _ else _) at spec
    rw [ite_eq_right small] at spec
    rcases outcome.status with failed | accepted | rejected
    · rw [ite_eq_right (by omega : result.status ≠ 3)]
      have prime : Spec.Dsa.probablePrime (P.value counter) (P.context.witnesses.bytes.drop used) = none := by
        simpa [PSearchPlan.value, primeRunResult, failed] using spec.symm
      have answer : expected = none := by rw [remaining, P.remaining_step bound, ite_eq_right small, prime]
      exact ⟨Wt, result.used, memory, cursorT, outcome.bound,
        .inl ⟨by rw [statusT, failed]; rfl, answer⟩, total, rdt, wrt⟩
    · rw [ite_eq_right (by omega : result.status ≠ 3)]
      have prime : Spec.Dsa.probablePrime (P.value counter) (P.context.witnesses.bytes.drop used) =
          some (true, P.context.witnesses.bytes.drop result.used) := by
        simpa [PSearchPlan.value, primeRunResult, accepted] using spec.symm
      have answer : expected = some (some (P.value counter), P.context.witnesses.bytes.drop result.used) := by
        rw [remaining, P.remaining_step bound, ite_eq_right small, prime]
        rfl
      obtain ⟨D, prepared⟩ := outcome.accepted accepted
      exact ⟨Wt, result.used, memory, cursorT, outcome.bound,
        .inr (.inr ⟨P.value counter, by rw [statusT, accepted]; rfl, answer, ⟨D, prepared, pb, eb⟩⟩), total, rdt, wrt⟩
    · rw [ite_eq_left rejected]
      have prime : Spec.Dsa.probablePrime (P.value counter) (P.context.witnesses.bytes.drop used) =
          some (false, P.context.witnesses.bytes.drop result.used) := by
        simpa [PSearchPlan.value, primeRunResult, rejected] using spec.symm
      have next : expected = P.remaining (counter + 1) result.used := by
        rw [remaining, P.remaining_step bound, ite_eq_right small, prime]
        rfl
      exact ⟨Wt, result.used, memory, cursorT, outcome.bound,
        fun _ => by rw [statusT, rejected]; rfl, next, total, rdt, wrt⟩
end VG.Proof.Dsa.X86.Generation
