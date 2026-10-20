module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterState
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterStable
import VerifiedGarbage.Proof.Dsa.X86.Generation.ParameterStep
import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchSlots
import VerifiedGarbage.Proof.Dsa.X86.Generation.TapeLoop

/-! # Complete native parameter search over finite seed, h, and witness tapes -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash)
open VG.Proof.Pbkdf2.Stream.X86 VG.Impl.Dsa.X86.Generation

theorem nativeParameterSearch_ok {H : Hash} (Khash : HashOK H) (F : KeyRandom.CheckCall.CheckFn)
    {P : SearchContextPlan} {W : Nat → BitVec 32} {s : State} {used : Nat}
    (R : SearchContext P W s) (cursor : W 16 = BitVec.ofNat 32 used) (bound : used ≤ P.witnesses.bytes.length)
    (digest : H.D = P.geometry.qLen) (final : H.F = P.geometry.qLen)
    (hash : ∀ bs, Khash.SH.H.hash bs = Spec.Dsa.seedHash (8 * P.geometry.qLen) bs)
    (hashSize : ∀ bs, (Spec.Dsa.seedHash (8 * P.geometry.qLen) bs).length = P.geometry.qLen) :
    WP isa (parameterSearch H P.geometry.pLen P.geometry.qLen
      (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen)) s
      (ParameterFinished P (parameterRemaining P 0 used) s) := by
  let I := ParameterInvariant P (parameterRemaining P 0 used) s
  let Q := ParameterFinished P (parameterRemaining P 0 used) s
  have driver : TapeDriver seedTape P.geometry.frameBase P.geometry.qLen P.seeds.bytes.length
      (parameterBody H P.geometry.pLen P.geometry.qLen (finishDomain F.name F.code P.geometry.pLen P.geometry.qLen)) I Q :=
    { baseBound := by decide
      totalBound := by decide
      usedBound := by decide
      pointerBound := by decide
      widthBound := by have := P.geometry.qWidth; omega
      widthPositive := by have := P.geometry.qWidth; omega
      totalFits := P.seeds.size
      stable := parameterInvariant_stable P (parameterRemaining P 0 used) s
      finish := parameterFinished_stable P (parameterRemaining P 0 used) s
      view := by
        rintro n t ⟨Wt, _, Rt, seed, _, _, _, _, _, _, _⟩
        exact ⟨Wt, Rt.arena.frame, Rt.representation, seed,
          (Rt.fixed 9 (by decide) (by decide)).trans P.seedLength⟩
      done := by
        intro n a b Wt hi exhausted _ rep _ repT O K
        exact parameter_done hi exhausted rep repT O K
      step := by
        intro n a b Wt hi available _ rep _ _ repT O K
        have seedBound : n ≤ P.seeds.bytes.length := by
          obtain ⟨_, _, _, _, _, _, h, _⟩ := hi
          exact h
        exact parameter_step Khash F digest final hash hashSize hi (by omega) rep repT O K }
  unfold parameterSearch
  apply driver.run_ok R.arena.frame R.representation
  intro t _ repT O K
  have Rt := R.slot (by decide : 10 < 37) (by decide) repT O K (by decide)
  exact ⟨_, used, Rt, rfl, cursor, bound, Nat.zero_le _, rfl,
    parameter_frame O (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide), K.2.1, K.2.2⟩
end VG.Proof.Dsa.X86.Generation
