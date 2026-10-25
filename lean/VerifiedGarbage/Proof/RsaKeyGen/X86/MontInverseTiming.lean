module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.MontInverse
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Full inverse setup uses a fixed native multiplication schedule -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.MontInverse
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.MontInverse

theorem code_trace (modulus inverse : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code modulus inverse)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (code modulus inverse) (code 0 0)
    (.seq (roundTaint [.edi]) (.block []) (.block [])) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.MontInverse
