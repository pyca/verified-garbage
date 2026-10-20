module
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateCT
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateArguments
public import VerifiedGarbage.Impl.Dsa.X86.Generation.CandidateArguments
import VerifiedGarbage.Proof.Dsa.X86.Generation.CandidateCT

/-! # Public saved pointers are the only inputs controlling candidate arithmetic timing -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

def CandidateArgsAt (p : PublicFrame) (s : State) : Prop :=
  s.gpr .esi = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.shaped ∧
  s.gpr .ecx = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.q ∧
  s.gpr .edi = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.arithmetic

theorem candidateArgs_ct : RelCT isa (Two (FrameAt [5])) (.block candidateArgs) (Two CandidateArgsAt) := by
  refine two_piece [.esp] (frameAt_pins _) (by taint_decide) ?_
  intro p s R
  refine WP.mono (candidateArgs_ok R.1 (R.2 5 (by simp))) fun t ⟨si, cx, di, _, _⟩ => ?_
  exact ⟨si, cx, di⟩

theorem candidateComputeFromFrame_ct (plen qlen n : Nat)
    (sizes : (plen = 128 ∧ qlen = 20 ∧ n = 16) ∨ (plen = 256 ∧ qlen = 32 ∧ n = 32) ∨
      (plen = 384 ∧ qlen = 32 ∧ n = 48)) :
    RelCT isa (Two (FrameAt [5])) (candidateComputeFromFrame plen qlen n) (fun _ _ => True) := by
  refine RelCT.seq candidateArgs_ct ((candidateCompute_ct plen qlen n sizes).mono ?_ (fun _ _ h => h))
  rintro s t ⟨p, hs, ht⟩ r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  exacts [hs.2.2.trans ht.2.2.symm, hs.1.trans ht.1.symm, hs.2.1.trans ht.2.1.symm]
end VG.Proof.Dsa.X86.Generation
