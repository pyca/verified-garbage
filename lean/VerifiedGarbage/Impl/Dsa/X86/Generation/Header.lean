module

public import VerifiedGarbage.Impl.Rsa.X86.KeyRt

/-! # Initialize scalar fields in the reused RSA arithmetic workspace -/

@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86

def setHeader (d value : Nat) : List Instr :=
  [.mov .eax (.imm (BitVec.ofNat 32 value)), .store (sc d) .eax]

end VG.Impl.Dsa.X86.Generation
