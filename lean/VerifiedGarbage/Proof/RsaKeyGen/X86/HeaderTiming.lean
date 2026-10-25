module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Header
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Prepared metadata initialization has no secret-dependent address -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Header
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Header

theorem code_trace (w : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (.block (code w))
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (.block (code w)) (.block (code 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Header
