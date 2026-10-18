module

public import VerifiedGarbage.Impl.Bignum.X86.ArrayCompare

/-! # Validate public packed-key arithmetic preconditions before exponentiation -/

@[expose] public section
namespace VG.Impl.Bignum.X86.PublicContext
open VG VG.X86 VG.Impl.Mont.X86

def precomputedCheckOffset : Nat := 148

def precomputedCheckFinish (n : Nat) : List Instr :=
  [.mov .edx (.mem (sc precomputedCheckOffset)), .alu .and .ecx (.reg .edx),
   .mov .eax (.mem (sc (slot n 0))), .alu .and .eax (.imm 1),
   .alu .and .ecx (.reg .eax), .alu .cmp .ecx (.imm 0)]

def precomputedCheckFirst (n : Nat) : Prog isa :=
  .seq (Dynamic.one n (slot n 4))
    (.seq (arrayCompare n 4 0) (.block [.store (sc precomputedCheckOffset) .ecx]))

def precomputedChecks (n : Nat) : Prog isa :=
  .seq (precomputedCheckFirst n) (.seq (arrayCompare n 5 0) (.block (precomputedCheckFinish n)))

end VG.Impl.Bignum.X86.PublicContext
