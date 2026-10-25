module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # A masked exponent halving always visits every native word -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.HalfPass
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.HalfPass

theorem code_trace (n src out : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code n src out)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code n src out) (code 1 0 0)
    (VG.Taint.hintOf taint (roundTaint [.edi]) (Code.erase (code 1 0 0)))
    (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.HalfPass
