module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorRangeCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorAcceptedCT
public import Aesop.BuiltinRules
public import Mathlib.Tactic.ToDual
public import VerifiedGarbage.Spec.Weierstrass.Point
public import VerifiedGarbage.Impl.Dsa.X86.Generation.GeneratorSearch
public import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorCTState
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorAcceptedCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.GeneratorRangeCT

/-! # Both generator range branches have public traces -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem generatorCandidate_ct (G : PrimeConfig) : RelCT isa (Two (GeneratorCandidateAt G))
    (generatorCandidate G.len) (fun _ _ => True) := by
  unfold generatorCandidate
  refine RelCT.seq (generatorRange_ct G) ?_
  apply two_ite (fun _ _ _ hs ht => by simp only [eval, hs.zero, ht.zero])
  · refine two_taint [.esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    obtain rfl := List.mem_singleton.mp hr
    obtain ⟨Ws, Rs⟩ := hs.1.resources
    obtain ⟨Wt, Rt⟩ := ht.1.resources
    exact BitVec.eq_of_toNat_eq (Rs.searchFrame.esp_toNat.trans Rt.searchFrame.esp_toNat.symm)
  · exact (generatorAccepted_ct G).mono (fun _ _ => two_mono (fun _ _ h => h.1)) (fun _ _ h => h)
end VG.Proof.Dsa.X86.Generation
