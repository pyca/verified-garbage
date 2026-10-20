module
public import VerifiedGarbage.Impl.Dsa.X86.Generate
public import VerifiedGarbage.Impl.Dsa.X86.Generation.Shape

/-! # Copy the low candidate bytes and set its required endpoint bits -/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86

def pShapeArgs (len : Nat) : List Instr :=
  [.mov .edx (.reg .edi), .mov .ecx (.imm (BitVec.ofNat 32 len)), .mov .ebx (.imm (-1))]

def pShape (len : Nat) : Prog isa :=
  .seq (.block (pShapeArgs len)) (.seq Generate.copyMasked (shape len))
end VG.Impl.Dsa.X86.Generation
