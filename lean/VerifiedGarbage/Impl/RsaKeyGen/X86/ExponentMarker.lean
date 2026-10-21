module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowPair
public import VerifiedGarbage.Impl.RsaKeyGen.X86.LowBit

/-! # Compute the exponent's alignment marker by a fixed masked word scan -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentMarker
open VG VG.X86

def code (src count : Nat) : Prog isa := .seq (LowPair.scan src count) (.block LowBit.code)

end VG.Impl.RsaKeyGen.X86.ExponentMarker
