module
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ConstructWrites
import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.DrawMemory
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributionReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPConstruct

/-! # Constructing a p candidate preserves the search context and accepted q -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem searchConstruct_ok {H : Hash} (K : HashOK H) {P : SearchContextPlan} {T : GenerationTape P.geometry}
    {W : Nat → BitVec 32} {s : State} {offset qvalue : Nat}
    (R : SearchContext P W s) (seed : TapeMemory T s) (len : T.bytes.length = P.geometry.qLen)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (offsetBound : offset + P.geometry.contributionCount < 2 ^ 24)
    (source : W 1 = T.pointer) (offsetValue : W 2 = BitVec.ofNat 32 offset)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) = qvalue)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (P.geometry.pLen / 8))))
    (hash : ∀ bs, K.SH.H.hash bs = Spec.Dsa.seedHash (8 * T.bytes.length) bs)
    (hashSize : ∀ bs, 8 * (Spec.Dsa.seedHash (8 * T.bytes.length) bs).length = 8 * T.bytes.length) :
    WP isa (pConstruct H P.geometry.pLen P.geometry.qLen) s fun t =>
      let value := Spec.Dsa.pCandidate (8 * P.geometry.pLen) (8 * P.geometry.qLen) qvalue T.bytes offset
      Spec.Rsa.bytesAt t.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen value ∧
      Spec.Rsa.bytesAt t.mem (off P.geometry.base exponent) P.geometry.pLen =
        Spec.Dsa.encodeBE P.geometry.pLen ((value - 1) / qvalue) ∧
      Spec.Dsa.decodeBE (Spec.Rsa.bytesAt t.mem (off P.geometry.base q) P.geometry.qLen) = qvalue ∧
      SearchContext P W t ∧ TapeMemory T t ∧
      Frame (constructionWrites K P.geometry T offset) s.mem t.mem ∧
      Keeps [.eax, .ebx, .ecx, .edx, .esi, .edi, .ebp] s t := by
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have C := contributionReady K R.arena R.representation len final source
    ((R.fixed 3 (by decide) (by decide)).trans P.wrapped)
    ((R.fixed 4 (by decide) (by decide)).trans P.hashesValue)
    ((R.fixed 14 (by decide) (by decide)).trans P.hashPointer) offsetValue
    (by intro i hi; exact seed.read i 1 (by omega)) (by intro i hi; exact seed.byte hi)
  have inputs := generationPConstructInputs K R.arena C len digest final offsetBound
    ((R.representation 5 (by decide)).trans parent) qval qpos qbound
  refine WP.mono (pConstruct_ok inputs hash hashSize) fun t ⟨pb, eb, _, O, Kt⟩ => ?_
  have F := O.sub (construction_mutable K P.geometry T offset len final)
  refine ⟨pb, eb, ?_, R.frame (R.representation.keep O (construction_frameApart inputs))
    (fun _ _ _ => rfl) F Kt (by decide), seed.keep F T.parameterApart Kt, O, Kt⟩
  rw [drawFrame_bytes O (construction_qApart inputs) (by have := P.geometry.qWidth; omega), qval]
end VG.Proof.Dsa.X86.Generation
