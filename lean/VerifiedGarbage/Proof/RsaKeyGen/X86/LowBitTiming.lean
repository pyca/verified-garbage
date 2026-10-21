module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.Dsa.X86.TimingBlocks

/-! # The native paired low-bit operation has a fixed instruction trace -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.LowBit
open VG VG.X86 VG.Proof.Dsa.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.LowBit

theorem code_trace : RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (.block code)
    (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  checkedBlockInvariant rfl rfl

end VG.Proof.RsaKeyGen.X86.LowBit
