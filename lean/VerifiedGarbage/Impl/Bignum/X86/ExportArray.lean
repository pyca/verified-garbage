module

public import VerifiedGarbage.Impl.Bignum.X86.CopyBytes

/-! # Export packed workspace limbs in their little-endian byte order -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def exportArrayArgs (n src : Nat) : List Instr :=
  [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 src)),
   .mov .ecx (.imm (BitVec.ofNat 32 (8 * n)))]

/-- EBX points at the output and is advanced by `8*n` bytes. -/
def exportArray (n src : Nat) : Prog isa := .seq (.block (exportArrayArgs n src)) copyBytes

end VG.Impl.Bignum.X86
