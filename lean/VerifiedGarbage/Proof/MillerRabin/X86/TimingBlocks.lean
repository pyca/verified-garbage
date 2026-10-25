module

public import VerifiedGarbage.Impl.MillerRabin.X86.Round
public import VerifiedGarbage.Proof.Framework.X86.Taint
public import VerifiedGarbage.Proof.Framework.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Secret digit and flag arithmetic has no secret-dependent trace -/

@[expose] public section
namespace VG.Proof.MillerRabin.X86
open VG VG.X86 VG.Impl.MillerRabin.X86 VG.Proof.Dsa.X86

/-- Only explicitly listed registers and the stack pointer are public.
Workspace metadata is republished from its correctness invariant after loads. -/
def roundTaint (rs : List Reg := []) (flags : Bool := false) : VG.X86.Taint.T :=
  { regs := .ofList (.esp :: rs), flags := flags }

theorem squareFlag_relCT : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block squareFlag) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi]) rfl rfl

theorem windowEnd_relCT : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block windowEnd) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant (τ' := roundTaint [.edi]) rfl rfl

theorem maskIndex_relCT (j : Nat) : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi]))
    (.block (maskIndex j)) (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (maskIndex j)) (.block (maskIndex 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl)

end VG.Proof.MillerRabin.X86
