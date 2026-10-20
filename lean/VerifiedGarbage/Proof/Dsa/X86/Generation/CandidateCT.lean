module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateCompute
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.LeafCT
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateCompute
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! # Candidate construction uses fixed-width division with public pointers -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation

theorem candidateCompute_ct (plen qlen n : Nat)
    (sizes : (plen = 128 ∧ qlen = 20 ∧ n = 16) ∨ (plen = 256 ∧ qlen = 32 ∧ n = 32) ∨
      (plen = 384 ∧ qlen = 32 ∧ n = 48)) :
    RelCT isa (RegistersAgree [.edi, .esi, .ecx]) (candidateCompute plen qlen n) (fun _ _ => True) := by
  rcases sizes with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals exact RelCT.taint (A := taint) (τr [.edi, .esi, .ecx]) (fun _ _ h => agree_regs h) (by taint_decide)
end VG.Proof.Dsa.X86.Generation
