module
public import Aesop.BuiltinRules
public import Batteries.Tactic.Init
public import Batteries.Tactic.PermuteGoals
public import Batteries.Tactic.SeqFocus
public import Mathlib.Tactic.ToDual
public import Mathlib.Util.CompileInductive
public import VerifiedGarbage.Proof.Framework.GetElem
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorInvariant
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorSearchStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeLoop

/-! # Complete native generator search, including retries and finite-tape exhaustion -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem nativeGenerator_ok {P : GeneratorSearchPlan} {W : Nat → BitVec 32} {s : State}
    (R : GeneratorSearchMemory P W s) :
    WP isa (nativeGenerator P.core.len) s (GeneratorFinished P (P.remaining 0) s) := by
  let I := GeneratorInvariant P (P.remaining 0) s
  let Q := GeneratorFinished P (P.remaining 0) s
  have driver : TapeDriver generatorTape P.frame P.core.len P.tape.length (generatorBody P.core.len) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      widthBound := by have := P.core.lenMax; omega
      widthPositive := by have := P.core.lenMin; omega
      totalFits := P.tapeFits
      stable := generatorInvariant_stable P (P.remaining 0) s
      finish := generatorFinished_stable P (P.remaining 0) s
      view := by
        rintro used t ⟨Wt, Rt, usedValue, _, _, _, _⟩
        exact ⟨Wt, Rt.layout, Rt.representation, usedValue,
          (Rt.fixed 12 (by decide) (by decide)).trans P.savedTotal⟩
      done := by
        intro used u v Wt hi hex _ rep _ repT O K
        exact generator_done hi hex rep repT O K
      step := by
        intro used u v Wt hi hav _ rep _ _ repT O K
        exact generator_search_step hi (by have := P.core.lenMin; omega) rep repT O K }
  unfold nativeGenerator
  apply driver.run_ok R.layout R.representation
  intro t _ repT O K
  have Rt := R.control repT (by
    intro i _ hx
    have ne : i ≠ 20 := by intro eq; subst i; simp at hx
    change frameUpdate W 20 0 i = W i
    simp only [frameUpdate, ite_eq_right ne]) O (by unfold generatorTape frameBytes; decide) K (by decide)
  exact ⟨_, Rt, rfl, rfl, generator_search_frame O (by unfold generatorTape frameBytes; decide), K.2.1, K.2.2⟩
end VG.Proof.Dsa.X86.Generation
