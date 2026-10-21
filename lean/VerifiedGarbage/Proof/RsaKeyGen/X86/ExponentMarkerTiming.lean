module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.ExponentMarker
public import VerifiedGarbage.Proof.MillerRabin.X86.TimingBlocks
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowPairTiming
import VerifiedGarbage.Proof.RsaKeyGen.X86.LowBitTiming

/-! # The secret exponent alignment is prepared without secret-dependent leakage -/

@[expose] public section
namespace VG.Proof.RsaKeyGen.X86.ExponentMarker
open VG VG.X86 VG.Proof.MillerRabin.X86 VG.Impl.RsaKeyGen.X86.ExponentMarker

theorem code_trace (src count : Nat) :
    RelCT isa (VG.X86.Taint.Agree (roundTaint [.edi])) (code src count)
      (VG.X86.Taint.Agree (roundTaint [.edi])) :=
  RelCT.seq (LowPair.scan_trace src count) LowBit.code_trace

end VG.Proof.RsaKeyGen.X86.ExponentMarker
