module

public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # A native scan for a nonzero low part of a candidate difference -/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.OrScan
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def code (n src : Nat) : Prog isa :=
  .seq (.block [.mov .ebx (.imm 0)]) (wordLoop n [.alu .or .ebx (.mem (at_ .ebp src))])

end VG.Impl.RsaKeyGen.X86.OrScan
