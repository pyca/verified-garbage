module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks
import VerifiedGarbage.Proof.Framework.KernelRfl

/-! # Both fallback choices execute identical native updates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem codeAt_trace (k src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (codeAt k src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (codeAt k src)) (.block (codeAt 2 0)) (.block []) (by kernel_rfl) (by kernel_rfl) (by kernel_rfl) (by decide +kernel)

theorem code_trace (w src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (code w src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  codeAt_trace (2 * w) src

end VG.Proof.RsaKeyGen.X86.WitnessFallback
