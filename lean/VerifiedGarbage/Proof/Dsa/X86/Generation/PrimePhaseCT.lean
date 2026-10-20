module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativePSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchInitCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGeneratorCT
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorPhaseCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.NativePSearchCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable

/-! # Public p-search success selects a public generator-search modulus and witness cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def searchOutcomeStatus {α : Type} (expected : Option (Option α × List Byte)) : BitVec 32 :=
  match expected with | none => 0 | some (none, _) => 3 | some (some _, _) => 1

def PrimePhaseAfter (P : PSearchPlan) (used : Nat) (s : State) : Prop :=
  ∃ initial, PSearchFinished P (P.remaining 0 used) initial s

theorem primePhaseAfter_view {P : PSearchPlan} {used : Nat} {s : State} (H : PrimePhaseAfter P used s) :
    SearchFrame s P.context.geometry.frameBase ∧
      s.mem.readW (off P.context.geometry.frameBase 76) 32 = searchOutcomeStatus (P.remaining 0 used) := by
  obtain ⟨_, W, _, R, _, _, result, _, _, _⟩ := H
  refine ⟨R.context.arena.frame, ?_⟩
  rw [R.context.representation 19 (by decide)]
  rcases result with ⟨status, expected⟩ | ⟨status, expected⟩ | ⟨value, status, expected, _⟩ <;>
    rw [expected] <;> exact status

theorem primePhaseAfter_keep {P : PSearchPlan} {used : Nat} {s t : State}
    (H : PrimePhaseAfter P used s) (mem : t.mem = s.mem) (K : Keeps [.eax] s t) : PrimePhaseAfter P used t := by
  obtain ⟨initial, R⟩ := H
  exact ⟨initial, pSearchFinished_stable P (P.remaining 0 used) initial R
    (by rw [mem]; exact Outside.refl _ _ _ _) (K.mono (by decide))⟩

theorem primePhaseAfter_success {P : PSearchPlan} {used value : Nat} {rest : List Byte} {s : State}
    (expected : P.remaining 0 used = some (some value, rest)) (H : PrimePhaseAfter P used s) :
    SearchGeneratorAt P value (P.context.witnesses.bytes.length - rest.length) s := by
  obtain ⟨_, W, next, R, cursor, bound, result, _, _, _⟩ := H
  rcases result with ⟨_, bad⟩ | ⟨_, bad⟩ | ⟨v, _, good, A⟩
  · simp [expected] at bad
  · simp [expected] at bad
  · rw [expected, Option.some.injEq, Prod.mk.injEq, Option.some.injEq] at good
    obtain ⟨rfl, tails⟩ := good
    have length := congrArg List.length tails
    simp only [List.length_drop] at length
    have nextEq : next = P.context.witnesses.bytes.length - rest.length := by omega
    exact ⟨⟨W, R, by rw [← nextEq]; exact cursor⟩, A⟩

theorem primePhase_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (P : PSearchPlan) (used : Nat) (bound : used ≤ P.context.witnesses.bytes.length)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => PSearchStartAt P used)
      (.seq (nativePSearch H P.context.geometry.pLen P.context.geometry.qLen)
        (onSuccess (.seq (nativeGenerator P.context.geometry.pLen)
          (onSuccess (finishDomain F.name F.code P.context.geometry.pLen P.context.geometry.qLen))))) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => PrimePhaseAfter P used)
    (nativePSearch_ct K P used bound digest final hash hashSize) ?_)
    (onSuccess_ct (fun (_ : Unit) => P.context.geometry.frameBase) (fun _ => searchOutcomeStatus (P.remaining 0 used))
      (fun _ _ h => primePhaseAfter_view h) (fun _ _ _ h mem K => primePhaseAfter_keep h mem K) ?_)
  · rintro _ s ⟨W, R, cursor⟩
    exact WP.mono (nativePSearch_ok K R cursor bound digest final hash hashSize) fun _ h => ⟨s, h⟩
  · cases expected : P.remaining 0 used with
    | none =>
      apply RelCT.of_false
      rintro s t ⟨_, hs, _⟩
      have impossible : (0 : BitVec 32) = 1 := by simpa only [expected, searchOutcomeStatus] using hs.2
      exact (by decide : (0 : BitVec 32) ≠ 1) impossible
    | some pair =>
      obtain ⟨value, rest⟩ := pair
      cases value with
      | none =>
        apply RelCT.of_false
        rintro s t ⟨_, hs, _⟩
        have impossible : (3 : BitVec 32) = 1 := by simpa only [expected, searchOutcomeStatus] using hs.2
        exact (by decide : (3 : BitVec 32) ≠ 1) impossible
      | some value =>
        exact (generatorPhase_ct F P value (P.context.witnesses.bytes.length - rest.length)).mono
          (fun _ _ => two_mono (fun _ _ h => primePhaseAfter_success expected h.1)) (fun _ _ h => h)
end VG.Proof.Dsa.X86.Generation
