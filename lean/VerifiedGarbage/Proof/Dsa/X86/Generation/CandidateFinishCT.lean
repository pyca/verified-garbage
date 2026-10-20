module
public import Mathlib.Tactic.Set
public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Spec.Weierstrass
import VerifiedGarbage.Proof.Framework.Offset
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Proof.Dsa.X86.Generation.ArenaReady
public import VerifiedGarbage.Proof.Dsa.X86.RandomTwo
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateFromFrame
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateFromFrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateStoresCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeometrySeparate

/-! # Candidate division and persistence have fixed-width public-address traces -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation VG.Impl.Dsa.Generation.Layout

def CandidateFinishAt (G : GenerationGeometry) (qvalue : Nat) (s : State) : Prop :=
  ArenaReady G s ∧ s.mem.readW (off G.frameBase 20) 32 = G.parent ∧
    Spec.Dsa.decodeBE (Spec.Rsa.bytesAt s.mem (off G.base q) G.qLen) = qvalue

theorem candidateFinish_ct (G : GenerationGeometry) (qvalue : Nat) (positive : 0 < qvalue)
    (bound : 2 * qvalue < 2 ^ (32 * (2 * (G.pLen / 8)))) :
    RelCT isa (Two fun (_ : Unit) => CandidateFinishAt G qvalue)
      (.seq (candidateComputeFromFrame G.pLen G.qLen (G.pLen / 8)) (candidateStores G.pLen)) (fun _ _ => True) := by
  have sizes : (G.pLen = 128 ∧ G.qLen = 20 ∧ G.pLen / 8 = 16) ∨
      (G.pLen = 256 ∧ G.qLen = 32 ∧ G.pLen / 8 = 32) ∨
      (G.pLen = 384 ∧ G.qLen = 32 ∧ G.pLen / 8 = 48) := by
    rcases G.lengths with h | h | h
    · exact .inl ⟨h.1, h.2, by rw [h.1]⟩
    · exact .inr (.inl ⟨h.1, h.2, by rw [h.1]⟩)
    · exact .inr (.inr ⟨h.1, h.2, by rw [h.1]⟩)
  refine RelCT.seq (two_post (Ψ := fun (_ : Unit) => CandidateStoresAt G.pLen G)
    (two_map (fun (_ : Unit) => (⟨G.frameBase, fun _ => G.parent⟩ : PublicFrame)) ?_
      (candidateComputeFromFrame_ct _ _ _ sizes)) ?_)
    (two_map (fun (_ : Unit) => G) (fun _ _ h => h) (candidateStores_ct G.pLen))
  · intro _ s R
    refine ⟨R.1.frame, ?_⟩
    intro i hi
    obtain rfl := List.mem_singleton.mp hi
    exact R.2.1
  · intro _ s R
    refine WP.mono (candidateComputeFromFrame_ok R.1 R.2.1 R.2.2 positive bound)
      fun t ⟨_, _, Rt, di, O, _⟩ => ?_
    refine ⟨rfl, Rt, ?_, di⟩
    have room : arithmetic + arithmeticBytes ≤ usedBytes G.pLen := by unfold arithmetic arithmeticBytes usedBytes domainCheck; omega
    rw [O.readW (r := ⟨G.frameBase, VG.Impl.Dsa.X86.Generation.frameBytes⟩)
      (Offset.contains_base _ (by unfold VG.Impl.Dsa.X86.Generation.frameBytes; decide) (by decide))
      (by intro r hr; obtain rfl := List.mem_singleton.mp hr; exact G.frame_part room) (by decide)]
    exact R.2.1
end VG.Proof.Dsa.X86.Generation
