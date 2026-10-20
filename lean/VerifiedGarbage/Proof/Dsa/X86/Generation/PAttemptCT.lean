module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateTest
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateTestCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptConstructCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptReturnCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchValue

/-! # A complete p-search attempt has a trace determined by public inputs -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem candidateTestReturn_ct (P : SearchContextPlan) (value used : Nat)
    (bound : value < 256 ^ P.geometry.pLen) (odd : value % 2 = 1) (usedBound : used ≤ P.witnesses.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => PCandidateAt P value used)
      (.seq (pCandidateTest P.geometry.pLen) (.block pAttemptReturn)) (fun _ _ => True) := by
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => FrameAt [5] ⟨P.geometry.frameBase, P.saved⟩)
    (pCandidateTest_ct P value used bound odd usedBound) ?_)
    (two_map (fun (_ : Unit) => (⟨P.geometry.frameBase, P.saved⟩ : PublicFrame)) (fun _ _ h => h) pAttemptReturn_ct)
  rintro _ s ⟨W, R, usedValue, bytes⟩
  refine WP.mono (pCandidateTest_ok R bound odd bytes usedValue usedBound) fun t ⟨_, Rt, _, _, _⟩ => ?_
  refine ⟨Rt.arena.frame, ?_⟩
  intro i hi
  obtain rfl := List.mem_singleton.mp hi
  exact (Rt.representation 5 (by decide)).trans (Rt.fixed 5 (by decide) (by decide))

theorem pAttempt_ct {H : Hash} (K : HashOK H) (P : PSearchPlan) (counter used : Nat)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (counterBound : counter < 32 * P.context.geometry.pLen) (usedBound : used ≤ P.context.witnesses.bytes.length)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => PAttemptAt P counter used)
      (pAttempt H P.context.geometry.pLen P.context.geometry.qLen) (fun _ _ => True) := by
  have shape := P.value_shape counter hashSize
  exact RelCT.seq (pAttemptOffset_ct P counter used)
    (RelCT.seq (attemptConstruct_ct K P counter used digest final counterBound hash hashSize)
      (candidateTestReturn_ct P.context (P.value counter) used shape.1 shape.2 usedBound))
end VG.Proof.Dsa.X86.Generation
