module

public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-! # Import precomputed little-endian limbs into the i686 workspace -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def importArrayArgs (n dst : Nat) : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 dst)),
   .mov .ecx (.imm (BitVec.ofNat 32 (8 * n)))]

/-- ESI points at the input and is advanced by `8*n` bytes. -/
def importArray (n dst : Nat) : Prog isa := .seq (.block (importArrayArgs n dst)) copyBytes

end VG.Impl.Bignum.X86
