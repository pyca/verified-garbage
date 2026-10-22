module

public import VerifiedGarbage.Impl.Dsa.X86.Generation.Transfer
public import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Framework.RelCTAssoc
import VerifiedGarbage.Proof.Framework.KernelRfl
meta import VerifiedGarbage.Impl.Dsa.X86.Generation.Transfer
meta import VerifiedGarbage.Proof.Framework.X86.Taint
meta import VerifiedGarbage.Proof.Framework.X86.RelCT

/-! Fixed-width transfers expose only the public workspace pointer. -/

@[expose] public section
namespace VG.Proof.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Dsa.X86.Generation VG.Proof.Dsa.X86

private theorem copy_word_ct (o a : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc a)), .store (VG.Impl.Mont.X86.sc o) .eax])
    (VG.X86.Taint.Agree (τr [.edi])) :=
  erased_relCT _
    (.block [.mov .eax (.mem (VG.Impl.Mont.X86.sc 0)), .store (VG.Impl.Mont.X86.sc 0) .eax])
    (.block []) (by kernel_rfl) (by decide +kernel) (by decide +kernel) (by taint_decide)

theorem copy_words_ct (k o a : Nat) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (.block (VG.Impl.Weierstrass.X86.copy k o a)) (VG.X86.Taint.Agree (τr [.edi])) := by
  induction k generalizing o a with
  | zero => exact RelCT.block_nil (fun _ _ h => h)
  | succ k ih => exact RelCT.block_append (RelCT.seq (copy_word_ct o a) (ih _ _))

theorem transfer_words_ct (ts : List WordTransfer) : RelCT isa (VG.X86.Taint.Agree (τr [.edi]))
    (transferWords ts) (VG.X86.Taint.Agree (τr [.edi])) := by
  induction ts with
  | nil => exact RelCT.block_nil (fun _ _ h => h)
  | cons t ts ih => exact RelCT.seq (copy_words_ct t.words t.destination t.source) ih

end VG.Proof.Dsa.X86.Generation
