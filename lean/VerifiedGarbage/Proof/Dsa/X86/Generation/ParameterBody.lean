module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.ParameterSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PhaseResult
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePhase
import VerifiedGarbage.Proof.Dsa.X86.Generation.QPhase

/-! # A complete seed attempt matches the reviewed q, p, g, and domain-check specification -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def seedExpected (P : SearchContextPlan) (seed : List Byte) (used : Nat) :=
  VG.Proof.Dsa.Generation.seedResult (8 * P.geometry.pLen) (8 * P.geometry.qLen) seed
    ((Spec.Dsa.generationChunks P.geometry.pLen P.hs.bytes).map Spec.Dsa.decodeBE) (P.witnesses.bytes.drop used)

theorem parameterBody_ok {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    {P : SearchContextPlan} {T : GenerationTape P.geometry} {W : Nat → BitVec 32} {s : State} {used : Nat}
    (R : SearchContext P W s) (seed : TapeMemory T s) (len : T.bytes.length = P.geometry.qLen) (source : W 1 = T.pointer)
    (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.witnesses.bytes.length)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    WP isa (parameterBody H P.geometry.pLen P.geometry.qLen (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen)) s
      (PhaseResult P (W 10) (seedExpected P T.bytes used) s) := by
  unfold parameterBody
  refine WP.seq (WP.mono (qPhase_ok K R seed len source cursor bound digest final hash hashSize)
    fun b ⟨Wb, result, Rb, cursorB, statusB, _, boundB, statuses, spec, Ob, Kb⟩ => ?_)
  rcases statuses with failed | accepted | rejected
  · have prime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) (P.witnesses.bytes.drop used) = none := by
      simpa [primeRunResult, failed] using spec.symm
    have expected : seedExpected P T.bytes used = none := by unfold seedExpected VG.Proof.Dsa.Generation.seedResult; dsimp only; rw [prime]
    have status : Wb 19 = 0 := by rw [statusB, failed]; rfl
    have done : PhaseResult P (W 10) (seedExpected P T.bytes used) s b :=
      ⟨Wb, result.used, Rb.context, Rb.seedUsed, cursorB, boundB, .inl ⟨status, expected⟩, Ob, Kb.2.1, Kb.2.2⟩
    exact onSuccess_ok Rb.context.arena.frame Rb.context.representation
      (by intro t _ _ yes; rw [status] at yes; contradiction)
      (fun t mem K _ => phaseResult_stable _ _ _ _ done mem (K.mono (by decide)))
  · have prime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) (P.witnesses.bytes.drop used) =
        some (true, P.witnesses.bytes.drop result.used) := by simpa [primeRunResult, accepted] using spec.symm
    have expected : seedExpected P T.bytes used = (seedPlan P T len (W 10)).result result.used := by
      unfold seedExpected VG.Proof.Dsa.Generation.seedResult
      dsimp only
      rw [prime]
      rfl
    have status : Wb 19 = 1 := by rw [statusB, accepted]; rfl
    refine onSuccess_ok Rb.context.arena.frame Rb.context.representation (fun t mem Km _ => ?_)
      (by intro t _ _ no; exact False.elim (no status))
    have Rt := Rb.control (by rw [mem]; exact Outside.refl _ _ _ _) (Km.mono (by decide))
    have next := primePhase_ok K F Rt cursorB boundB digest final
      (by intro bs; change K.SH.H.hash bs = Spec.Dsa.seedHash (8 * T.bytes.length) bs; rw [len]; exact hash bs)
      (by intro bs; change 8 * (Spec.Dsa.seedHash (8 * T.bytes.length) bs).length = 8 * T.bytes.length; rw [len, hashSize])
    rw [← expected] at next
    exact WP.mono next fun u done => done.prepend (by rw [mem]; exact Ob) (Km.2.1.trans Kb.2.1) (Km.2.2.trans Kb.2.2)
  · have prime : Spec.Dsa.probablePrime (Spec.Dsa.qCandidate (8 * P.geometry.qLen) T.bytes) (P.witnesses.bytes.drop used) =
        some (false, P.witnesses.bytes.drop result.used) := by simpa [primeRunResult, rejected] using spec.symm
    have expected : seedExpected P T.bytes used = some (none, P.witnesses.bytes.drop result.used) := by
      unfold seedExpected VG.Proof.Dsa.Generation.seedResult; dsimp only; rw [prime]
    have status : Wb 19 = 3 := by rw [statusB, rejected]; rfl
    have done : PhaseResult P (W 10) (seedExpected P T.bytes used) s b :=
      ⟨Wb, result.used, Rb.context, Rb.seedUsed, cursorB, boundB, .inr (.inl ⟨status, expected⟩), Ob, Kb.2.1, Kb.2.2⟩
    exact onSuccess_ok Rb.context.arena.frame Rb.context.representation
      (by intro t _ _ yes; rw [status] at yes; contradiction)
      (fun t mem K _ => phaseResult_stable _ _ _ _ done mem (K.mono (by decide)))
end VG.Proof.Dsa.X86.Generation
