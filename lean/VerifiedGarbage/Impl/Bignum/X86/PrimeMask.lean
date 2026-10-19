module

public import VerifiedGarbage.Impl.Bignum.X86.SmallConstant
public import VerifiedGarbage.Impl.Mont.X86.Context
public import VerifiedGarbage.Impl.Dsa.X86.Checks

/-! # Validate a secret factor without a branch -/

@[expose] public section
namespace VG.Impl.Bignum.X86
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def primeMaskFinish (n : Nat) : List Instr :=
  [.mov .edx (.mem (sc (slot n 0))), .alu .and .edx (.imm 1),
    .mov .ecx (.imm 0), .alu .sub .ecx (.reg .edx), .alu .and .ecx (.reg .eax)]

/-- `ecx` is all ones precisely for odd factors greater than one. -/
def primeMask (n : Nat) : Prog isa :=
  .seq (smallConstant n (slot n 7) 1)
    (.seq (VG.Impl.Dsa.X86.lessThan n (slot n 7) (slot n 0)) (.block (primeMaskFinish n)))

end VG.Impl.Bignum.X86
