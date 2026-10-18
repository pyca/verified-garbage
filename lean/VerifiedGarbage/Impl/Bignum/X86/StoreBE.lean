module

public import VerifiedGarbage.Impl.Bignum.X86.ReverseBytes

/-! # Export an RSA workspace integer as big-endian bytes on i686

`edi` is the workspace, `ebx` the destination, and `ecx` the nonzero byte
count. The source integer starts at the public workspace offset `src`.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def storeBEArgs (src : Nat) : List Instr :=
  [.mov .esi (.reg .edi), .alu .add .esi (.imm (BitVec.ofNat 32 src)),
   .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]

def storeBE (src : Nat) : Prog isa := .seq (.block (storeBEArgs src)) reverseBytes

end VG.Impl.Bignum.X86
