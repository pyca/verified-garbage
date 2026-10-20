module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributions
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryContributionReady
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPConstruct
import VerifiedGarbage.Proof.Dsa.X86.Generation.PConstructCT

/-! # Instantiate candidate construction from public search state -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

def SearchConstructAt (P : SearchContextPlan) (T : GenerationTape P.geometry) (offset qvalue : Nat) (s : State) : Prop :=
  ∃ W, SearchContext P W s ∧ TapeMemory T s ∧ W 1 = T.pointer ∧ W 2 = BitVec.ofNat 32 offset ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) = qvalue

theorem searchConstruct_ct {H : Hash} (K : HashOK H) (P : SearchContextPlan) (T : GenerationTape P.geometry)
    (offset qvalue : Nat) (len : T.bytes.length = P.geometry.qLen)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (offsetBound : offset + P.geometry.contributionCount < 2 ^ 24)
    (qpos : 0 < qvalue) (qbound : 2 * qvalue < 2 ^ (32 * (2 * (P.geometry.pLen / 8)))) :
    RelCT isa (Two fun (_ : Unit) => SearchConstructAt P T offset qvalue)
      (pConstruct H P.geometry.pLen P.geometry.qLen) (fun _ _ => True) := by
  refine (pConstruct_ct K P.geometry (P.geometry.contributions T offset) qvalue).mono
    (fun _ _ => two_mono ?_) (fun _ _ h => h)
  rintro _ s ⟨W, R, seed, source, offsetValue, qval⟩
  have parent : W 5 = P.geometry.parent := (R.fixed 5 (by decide) (by decide)).trans P.parent
  have C := contributionReady K R.arena R.representation len final source
    ((R.fixed 3 (by decide) (by decide)).trans P.wrapped)
    ((R.fixed 4 (by decide) (by decide)).trans P.hashesValue)
    ((R.fixed 14 (by decide) (by decide)).trans P.hashPointer) offsetValue
    (by intro i hi; exact seed.read i 1 (by omega)) (by intro i hi; exact seed.byte hi)
  exact generationPConstructInputs K R.arena C len digest final offsetBound
    ((R.representation 5 (by decide)).trans parent) qval qpos qbound
end VG.Proof.Dsa.X86.Generation
