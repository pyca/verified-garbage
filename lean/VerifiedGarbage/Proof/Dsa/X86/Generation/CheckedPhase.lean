module
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PhaseResult
public import Aesop.BuiltinRules
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import Mathlib.Tactic.Attr.Core
import VerifiedGarbage.Proof.Dsa.X86.Generation.FinishDomain

/-! # A validated domain becomes the exact terminal or retry result of a seed phase -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

theorem checkedPhase_ok (F : KeyRandom.CheckCall.CheckFn) {P : SearchContextPlan} {W : Nat → BitVec 32}
    {s : State} {params : Spec.Dsa.Params} {used : Nat} (R : SearchContext P W s)
    (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.witnesses.bytes.length)
    (pb : Spec.Rsa.bytesAt s.mem (off P.geometry.base p) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen params.p)
    (qval : Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off P.geometry.base q) P.geometry.qLen) = params.q)
    (gb : Spec.Rsa.bytesAt s.mem (off P.geometry.base g) P.geometry.pLen = Spec.Dsa.encodeBE P.geometry.pLen params.g)
    (pBound : params.p < 256 ^ P.geometry.pLen) (qBound : params.q < 256 ^ P.geometry.qLen)
    (gBound : params.g < 256 ^ P.geometry.pLen) :
    WP isa (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen) s
      (PhaseResult P (W 10)
        (if Spec.Dsa.parametersValid params then some (some params, P.witnesses.bytes.drop used)
          else some (none, P.witnesses.bytes.drop used)) s) := by
  refine WP.mono (finishDomain_ok F R pb qval gb pBound qBound gBound) fun t ⟨Rt, bytes, O, K⟩ => ?_
  refine ⟨_, used, Rt, rfl, cursor, bound, ?_, O, K.2.1, K.2.2⟩
  by_cases valid : Spec.Dsa.parametersValid params
  · exact .inr (.inr ⟨params, by simp only [frameUpdate, ite_true, ite_eq_left valid],
      ite_eq_left valid, bytes⟩)
  · exact .inr (.inl ⟨by simp only [frameUpdate, ite_true, ite_eq_right valid], ite_eq_right valid⟩)
end VG.Proof.Dsa.X86.Generation
