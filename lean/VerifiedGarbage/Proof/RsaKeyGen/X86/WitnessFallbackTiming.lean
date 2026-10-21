module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.WitnessFallback
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # Both fallback choices execute identical native updates -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.WitnessFallback
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.WitnessFallback

theorem code_trace (w src : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block (code w src))
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  erased_relCT (.block (code w src)) (.block (code 1 0)) (.block []) rfl rfl rfl (by decide +kernel)

end VG.Proof.RsaKeyGen.X86.WitnessFallback
