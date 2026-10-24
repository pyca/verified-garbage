module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.KeyFinal
public import VerifiedGarbage.Proof.Rsa.X86.KeyTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.KeyConstantTiming

/-! # Final validity checks never branch on secret key values -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Key
open VG VG.X86 VG.Proof.Rsa.X86.Keys VG.Proof.Mont.X86.Dynamic
open VG.Impl.RsaKeyGen.X86.Key

theorem andFlag_public : KeyPublic andFlag :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem withFlag_public {c : Prog isa} (H : KeyPublic c) : KeyPublic (withFlag c) :=
  H.seq andFlag_public

theorem topBit_public (n : Nat) : KeyPublic (.block (topBit n)) := by
  refine ⟨.block [], workspaceTaint true, ?_, rfl⟩
  change taint.checkBlock (workspaceTaint true) (topBit n) = _
  rw [← VG.X86.Taint.checkBlock_erase _ _ (show VG.X86.Taint.noBases (workspaceTaint true) = true from rfl)]
  change taint.checkBlock (workspaceTaint true)
    [.mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .shift .shr .eax 31,
      .store (VG.Impl.Mont.X86.sc 0) .eax] = _
  rfl

theorem exponentUpper_public : KeyPublic (.block exponentUpper) :=
  ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem exponentAtLeastThree_public (n : Nat) : KeyPublic (exponentAtLeastThree n) := by
  refine (constArray_public ..).seq ((sub3_public ..).seq (KeyPublic.seq ?_ ?_))
  all_goals exact ⟨.block [], workspaceTaint true, rfl, rfl⟩

theorem finalMask_public (n : Nat) : KeyPublic (finalMask n) := by
  unfold finalMask
  apply KeyPublic.seqs
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · exact withFlag_public (topBit_public _)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public (bitOf_public ..)
  · exact withFlag_public exponentUpper_public
  · exact exponentAtLeastThree_public _

end VG.Proof.RsaKeyGen.X86.Key
