module
public import Aesop.BuiltinRules
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Proof.Dsa.X86.Generation.PreparedContext
public import VerifiedGarbage.Proof.Dsa.Generation.PDomain
import VerifiedGarbage.Proof.Framework.Offset
public import VerifiedGarbage.Proof.Dsa.X86.Generation.CheckPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometryPrime
public import VerifiedGarbage.Proof.Dsa.X86.Generation.SearchContext
import Mathlib.Tactic.Attr.Core

/-! # Candidate outcomes retain the prepared modulus only on acceptance -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86 VG.Impl.Dsa.Generation.Layout

def candidateTestWrites (G : GenerationGeometry) : List Region :=
  [G.part arithmetic arithmeticBytes, G.part witness 384,
   ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, below G.frame 16]

theorem candidateTest_frame (G : GenerationGeometry) :
    ∀ r ∈ [⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩], r ∈ candidateTestWrites G := by
  intro r hr; obtain rfl := List.mem_singleton.mp hr; simp [candidateTestWrites]

theorem candidateTest_prime (G : GenerationGeometry) (T : GenerationTape G) (len m : Nat)
    (lo : 4 ≤ len) (hi : len ≤ 384) (words : len % 4 = 0)
    (bits : Spec.RsaKeyGen.bitLength m = 8 * len) (odd : m % 2 = 1) :
    ∀ r ∈ checkPrimeWrites (G.prime T len m lo hi words bits odd) G.frameBase ((G.frame - 16).setWidth 64),
      ∃ outer ∈ candidateTestWrites G, r.Sub outer := by
  intro r hr
  change r ∈ [⟨(G.frame - 16).setWidth 64, 16⟩, G.part arithmetic arithmeticBytes,
    ⟨(G.pointer witness).setWidth 64, len⟩, ⟨off G.frameBase 64, 16⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact ⟨below G.frame 16, by simp [candidateTestWrites], fun _ h => h⟩
  · exact ⟨_, List.mem_cons_self, fun _ h => h⟩
  · rw [G.pointer_addr (by unfold witness usedBytes domainCheck; omega)]
    exact ⟨G.part witness 384, by simp [candidateTestWrites], fun _ h => by exact Nat.le_trans h hi⟩
  · exact ⟨⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩, by simp [candidateTestWrites],
      Offset.sub_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide)⟩

structure CandidateTestResult (P : SearchContextPlan) (value used : Nat) (result : PrimeStepResult) (s : State) : Prop where
  monotone : used ≤ result.used
  bound : result.used ≤ P.witnesses.bytes.length
  status : result.status = 0 ∨ result.status = 1 ∨ result.status = 3
  spec : if value < 2 ^ (8 * P.geometry.pLen - 1) then result.status = 3 ∧ result.used = used
    else primeRunResult P.witnesses.bytes result = Spec.Dsa.probablePrime value (P.witnesses.bytes.drop used)
  accepted : result.status = 1 → ∃ (D : VG.Proof.Dsa.Generation.PDomain P.geometry.pLen value),
    PrimePrepared (P.geometry.prime P.witnesses P.geometry.pLen value
      (by have := P.geometry.width; omega) (by have := P.geometry.width; omega)
      (by rcases P.geometry.width with h | h | h <;> rw [h] <;> decide) D.bits D.odd) s
end VG.Proof.Dsa.X86.Generation
