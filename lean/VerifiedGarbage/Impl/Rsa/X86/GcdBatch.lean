module

public import VerifiedGarbage.Impl.Weierstrass.X86.Inv
public import VerifiedGarbage.Impl.Weierstrass.X86.InvMemory
public import VerifiedGarbage.Impl.Rsa.X86.KeyWs

/-! # Helpers of the batched divstep GCD and inverse on i686

The mask of an even word, and the count of the batches down by one, which `InvBatchRt` and
`GcdBatchRt` share.
-/

@[expose] public section
namespace VG.Impl.Rsa.X86.GcdBatch
open VG VG.X86 VG.Impl.Mont.X86

/-- `ecx` all ones exactly when the word at the header's offset `src` is even. -/
def evenMask (src : Nat) : List Instr :=
 [.mov .ecx (.mem (sc src)),.alu .and .ecx (.imm 1),.alu .sub .ecx (.imm 1)]

/-- The count at the header's offset `d` down by one, its flags set by the new count. -/
def countDown (d : Nat) : List Instr :=
 [.mov .esi (.mem (sc d)),.alu .sub .esi (.imm 1),.store (sc d) .esi,.alu .test .esi (.reg .esi)]

end VG.Impl.Rsa.X86.GcdBatch
