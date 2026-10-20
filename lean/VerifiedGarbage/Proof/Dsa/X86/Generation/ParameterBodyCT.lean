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
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
public import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Hash
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccessCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PrimePhaseCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.QPhase
import VerifiedGarbage.Proof.Dsa.X86.Generation.QPhaseCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.QPhaseResultCT

/-! # Every decision in a complete seed attempt depends only on public generation tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def ParameterBodyAt (P : SearchContextPlan) (T : GenerationTape P.geometry) (seedUsed : BitVec 32)
    (used : Nat) (s : State) : Prop :=
  ∃ W, SearchContext P W s ∧ TapeMemory T s ∧ W 1 = T.pointer ∧ W 16 = BitVec.ofNat 32 used ∧ W 10 = seedUsed

theorem parameterBody_ct {H : Hash} (K : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    (P : SearchContextPlan) (T : GenerationTape P.geometry) (seedUsed : BitVec 32) (used : Nat)
    (len : T.bytes.length = P.geometry.qLen) (bound : used ≤ P.witnesses.bytes.length)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    RelCT isa (Two fun (_ : Unit) => ParameterBodyAt P T seedUsed used)
      (parameterBody H P.geometry.pLen P.geometry.qLen (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen))
      (fun _ _ => True) := by
  unfold parameterBody
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => QPhaseAfter P T len seedUsed used)
    ((qPhase_ct K P T used len bound digest final hash hashSize).mono
      (fun _ _ => two_mono (fun _ _ ⟨W, R, seed, source, cursor, _⟩ => ⟨W, R, seed, source, cursor⟩))
      (fun _ _ h => h)) ?_)
    (onSuccess_ct (fun (_ : Unit) => P.geometry.frameBase) (fun _ => primePublicStatus (qExpected P T used))
      (fun _ _ h => qPhaseAfter_view h) (fun _ _ _ h mem K => qPhaseAfter_keep h mem K) ?_)
  · rintro _ s ⟨W, R, seed, source, cursor, seedCursor⟩
    refine WP.mono (qPhase_ok K R seed len source cursor bound digest final hash hashSize)
      fun t ⟨W', result, Rt, cursorT, status, _, boundT, statuses, spec, _, _⟩ => ?_
    rw [seedCursor] at Rt
    exact ⟨W', result, Rt, cursorT, status, boundT, statuses, spec⟩
  · cases expected : qExpected P T used with
    | none =>
      apply RelCT.of_false
      rintro s t ⟨_, hs, _⟩
      have impossible : (0 : BitVec 32) = 1 := by simpa only [expected, primePublicStatus] using hs.2
      exact (by decide : (0 : BitVec 32) ≠ 1) impossible
    | some pair =>
      obtain ⟨accepted, rest⟩ := pair
      cases accepted with
      | false =>
        apply RelCT.of_false
        rintro s t ⟨_, hs, _⟩
        have impossible : (3 : BitVec 32) = 1 := by simpa only [expected, primePublicStatus] using hs.2
        exact (by decide : (3 : BitVec 32) ≠ 1) impossible
      | true =>
        exact (primePhase_ct K F (seedPlan P T len seedUsed) (P.witnesses.bytes.length - rest.length)
          (Nat.sub_le _ _) digest final
          (by intro bs; change K.SH.H.hash bs = Spec.Dsa.seedHash (8 * T.bytes.length) bs; rw [len]; exact hash bs)
          (by intro bs; change 8 * (Spec.Dsa.seedHash (8 * T.bytes.length) bs).length = 8 * T.bytes.length; rw [len, hashSize])).mono
          (fun _ _ => two_mono (fun _ _ h => qPhaseAfter_success expected h.1)) (fun _ _ h => h)
end VG.Proof.Dsa.X86.Generation
