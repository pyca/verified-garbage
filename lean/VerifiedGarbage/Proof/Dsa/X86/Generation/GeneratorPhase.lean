module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.Generation.SeedResult
import VerifiedGarbage.Proof.Dsa.Generation.GeneratorDomain
import VerifiedGarbage.Proof.Dsa.Encoding
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Validate
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchState
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PhaseResult
public import VerifiedGarbage.Proof.Dsa.X86.KeyRandom.CheckCall
import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckedPhase
import VerifiedGarbage.Proof.Dsa.X86.Generation.OnSuccess
import VerifiedGarbage.Proof.Dsa.X86.Generation.PSearchStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchGenerator

/-! # Search g, then return a checked domain or reject this seed -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout
open VG.Impl.Dsa.X86.Generation

def PSearchPlan.hs (P : PSearchPlan) : List Nat :=
  (Spec.Dsa.generationChunks P.context.geometry.pLen P.context.hs.bytes).map Spec.Dsa.decodeBE

theorem generatorPhase_ok (F : KeyRandom.CheckCall.CheckFn) {P : PSearchPlan} {value used : Nat}
    {W : Nat → BitVec 32} {s : State} (R : PSearchMemory P W s) (A : PSearchAccepted P value s)
    (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.context.witnesses.bytes.length) :
    WP isa (.seq (nativeGenerator P.context.geometry.pLen)
      (onSuccess (finishDomain F.name F.code P.context.geometry.pLen P.context.geometry.qLen))) s
      (PhaseResult P.context P.seedUsed
        (VG.Proof.Dsa.Generation.generatorResult value P.qvalue P.hs (P.context.witnesses.bytes.drop used)) s) := by
  refine WP.seq (WP.mono (searchGenerator_ok R A) fun b ⟨Wb, Rb, cursorB, pb, result, Ob, Kb⟩ => ?_)
  have cb : Wb 16 = BitVec.ofNat 32 used := cursorB.trans cursor
  have priorWrites := Ob.sub (generatorWrites_mutable P.context.geometry)
  rcases result with ⟨status, result⟩ | ⟨gvalue, status, result, gb⟩
  · change Spec.Dsa.generator value P.qvalue P.hs = _ at result
    have expected : VG.Proof.Dsa.Generation.generatorResult value P.qvalue P.hs (P.context.witnesses.bytes.drop used) =
        some (none, P.context.witnesses.bytes.drop used) := by
      unfold VG.Proof.Dsa.Generation.generatorResult
      change (match Spec.Dsa.generator value P.qvalue P.hs with | none => _ | some _ => _) = _
      rw [result]
    have done : PhaseResult P.context P.seedUsed
        (VG.Proof.Dsa.Generation.generatorResult value P.qvalue P.hs (P.context.witnesses.bytes.drop used)) s b :=
      ⟨Wb, used, Rb.context, Rb.seedUsed, cb, bound, .inr (.inl ⟨status, expected⟩), priorWrites, Kb.2.1, Kb.2.2⟩
    exact onSuccess_ok Rb.context.arena.frame Rb.context.representation
      (by intro t _ _ yes; rw [status] at yes; contradiction)
      (fun t mem K _ => phaseResult_stable _ _ _ _ done mem (K.mono (by decide)))
  · change Spec.Dsa.generator value P.qvalue P.hs = _ at result
    have expected : VG.Proof.Dsa.Generation.generatorResult value P.qvalue P.hs (P.context.witnesses.bytes.drop used) =
        if Spec.Dsa.parametersValid ⟨value, P.qvalue, gvalue⟩ then some (some ⟨value, P.qvalue, gvalue⟩, P.context.witnesses.bytes.drop used)
        else some (none, P.context.witnesses.bytes.drop used) := by
      unfold VG.Proof.Dsa.Generation.generatorResult
      change (match Spec.Dsa.generator value P.qvalue P.hs with | none => _ | some _ => _) = _
      rw [result]
    refine onSuccess_ok Rb.context.arena.frame Rb.context.representation (fun t mem K _ => ?_)
      (by intro t _ _ no; exact False.elim (no status))
    have Rt := Rb.control (by rw [mem]; exact Outside.refl _ _ _ _) (K.mono (by decide))
    have pBound : value < 256 ^ P.context.geometry.pLen := by
      have h := A.domain.upper
      rw [Nat.pow_mul] at h
      exact h
    have qBound : P.qvalue < 256 ^ P.context.geometry.qLen := by
      rw [← Rt.qval]
      have h := VG.Proof.Dsa.decodeBE_lt (Spec.Rsa.bytesAt t.mem (off P.context.geometry.base q) P.context.geometry.qLen)
      simpa only [Spec.Rsa.bytesAt, List.length_map, List.length_range] using h
    have gBound := (VG.Proof.Dsa.Generation.generator_bounds (by have := A.domain.large; omega : 0 < value) P.hs result).2
    have checked := checkedPhase_ok F (params := ⟨value, P.qvalue, gvalue⟩) Rt.context cb bound (by rw [mem]; exact pb) Rt.qval
      (by rw [mem]; exact gb) pBound qBound (Nat.lt_trans gBound pBound)
    rw [Rt.seedUsed, ← expected] at checked
    exact WP.mono checked fun u done => done.prepend (by rw [mem]; exact priorWrites)
      (K.2.1.trans Kb.2.1) (K.2.2.trans Kb.2.2)
end VG.Proof.Dsa.X86.Generation
