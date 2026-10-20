module
public meta import VerifiedGarbage.Proof.Framework.X86.RelCT
public meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Frame
public meta import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Dsa.X86.Generation.FrameCT
import VerifiedGarbage.Proof.Dsa.X86.Generation.BufferArgs
import VerifiedGarbage.Proof.Framework.RelCTAssoc
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PAttempt

/-! # Hand the public candidate status back to the bounded search controller -/
@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Proof.Mont VG.Proof.Mont.X86
open VG.Impl.Dsa.X86.Generation

theorem pAttemptReturn_ct : RelCT isa (Two (FrameAt [5])) (.block pAttemptReturn) (fun _ _ => True) := by
  unfold pAttemptReturn
  refine RelCT.block_append (RelCT.seq (two_piece (Ψ := fun p s =>
    s.gpr .edi = p.words 5 + BitVec.ofNat 32 VG.Impl.Dsa.Generation.Layout.control ∧
    SearchFrame s p.base) [.esp] (frameAt_pins _) (by taint_decide) ?_) ?_)
  · intro p s R
    refine WP.mono (bufferPointer_ok R.1 (R.2 5 (by simp)) .edi _) fun t ⟨di, _, K⟩ => ?_
    exact ⟨di, R.1.keeps K (by decide)⟩
  · refine two_taint [.edi, .esp] ?_ (by taint_decide)
    intro p s t hs ht r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hs.1.trans ht.1.symm
    · exact BitVec.eq_of_toNat_eq (hs.2.esp_toNat.trans ht.2.esp_toNat.symm)
end VG.Proof.Dsa.X86.Generation
