module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.Near
public import VerifiedGarbage.Proof.Framework.X86.RelCT
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # The RSA separation threshold comparison has no secret-dependent control -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.Near
open VG VG.X86 VG.Proof.Dsa.X86 VG.Impl.RsaKeyGen.X86.Near

theorem code_trace (n src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (τr [.esp, .edi])) (code n src)
      (VG.X86.Taint.Agree (τr [.esp, .edi])) :=
  erased_relCT (code n src) (code 0 0)
    (VG.Taint.hintOf taint (τr [.esp, .edi]) (code 0 0))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.Near
