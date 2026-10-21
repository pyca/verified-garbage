module

public import VerifiedGarbage.Impl.RsaKeyGen.X86.SigMask
public import VerifiedGarbage.Impl.RsaKeyGen.X86.HalfPass

/-! # Three masked passes align the exponent's final nonzero four-bit window -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.ExponentShift
open VG VG.X86

def halfIf (n marker out j : Nat) : Prog isa :=
  .seq (.block (SigMask.code marker j)) (HalfPass.code n out out)

def passes (n marker out : Nat) : Prog isa :=
  .seq (halfIf n marker out 1) (.seq (halfIf n marker out 2) (halfIf n marker out 3))

end VG.Impl.RsaKeyGen.X86.ExponentShift
