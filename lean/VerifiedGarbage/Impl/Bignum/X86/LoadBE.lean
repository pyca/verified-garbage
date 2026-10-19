module

public import VerifiedGarbage.Impl.Bignum.X86.ReverseBytes
public import VerifiedGarbage.Impl.Mont.X86.Words

/-! # Zero-extended import of arbitrary-length RSA integers on i686

The source pointer is in `esi` and its nonzero byte count in `ecx`.
The destination is `2*n` 32-bit limbs at workspace offset `out`.
-/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86

def loadBEArgs (out : Nat) : List Instr :=
  [.mov .ebx (.reg .edi), .alu .add .ebx (.imm (BitVec.ofNat 32 out)),
   .alu .add .esi (.reg .ecx), .alu .sub .esi (.imm 1)]

def loadBE (n out : Nat) : Prog isa :=
  .seq (VG.Impl.Mont.X86.Dynamic.zerosW out (2 * n))
    (.seq (.block (loadBEArgs out)) reverseBytes)

end VG.Impl.Bignum.X86
