module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Alignment masks use fixed addresses and no secret-dependent branches -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.SigMask
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.SigMask

theorem code_trace (marker j : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (code marker j))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (code marker j)) (.block (code 0 0)) (.block [])
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.SigMask
