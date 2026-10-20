module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.AttemptOffsetCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PCandidateTestCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchConstruct
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchConstructCT

/-! # Construct the public p candidate while preserving its witness cursor -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem attemptConstruct_ct {H : Hash} (K : HashOK H) (P : PSearchPlan) (counter used : Nat)
    (digest : H.D = P.context.geometry.qLen) (final : H.F = P.context.geometry.qLen)
    (counterBound : counter < 32 * P.context.geometry.pLen)
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * P.seed.bytes.length) bs).length = 8 * P.seed.bytes.length) :
    RelCT isa (Two fun (_ : Unit) => AttemptConstructAt P counter used)
      (pConstruct H P.context.geometry.pLen P.context.geometry.qLen)
      (Two fun (_ : Unit) => PCandidateAt P.context (P.value counter) used) := by
  refine two_post ((searchConstruct_ct K P.context P.seed _ P.qvalue P.seedLength digest final
    (P.context.geometry.contribution_offset counterBound) P.qPositive P.qBound).mono
    (fun _ _ => two_mono ?_) (fun _ _ h => h)) ?_
  · rintro _ s ⟨W, R, _, offset⟩
    exact ⟨W, R.context, R.seed, R.source, offset, R.qval⟩
  · rintro _ s ⟨W, R, usedValue, offset⟩
    refine WP.mono (searchConstruct_ok K R.context R.seed P.seedLength digest final
      (P.context.geometry.contribution_offset counterBound) R.source offset R.qval P.qPositive P.qBound hash hashSize)
      fun t ⟨bytes, _, _, Rt, _, _, _⟩ => ?_
    exact ⟨W, Rt, usedValue, bytes⟩
end VG.Proof.Dsa.X86.Generation
