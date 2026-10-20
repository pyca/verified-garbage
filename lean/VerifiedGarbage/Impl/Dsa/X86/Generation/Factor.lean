module
public import VerifiedGarbage.Impl.Dsa.X86.Generation.PrimeLayout
public import VerifiedGarbage.Impl.Mont.X86.Context

/-! # Strip powers of two from the candidate minus one

The candidate is odd and greater than three. Slot eight initially holds
its predecessor. At least one division is performed, and the public low
bit then controls further divisions. The count is saved for every round.
-/
@[expose] public section
namespace VG.Impl.Dsa.X86.Generation
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

def factorInit : List Instr := [.mov .ebx (.imm 0)]
def factorTest (n : Nat) : List Instr :=
  [.alu .add .ebx (.imm 1), .mov .eax (.mem (sc (slot n 8))), .alu .and .eax (.imm 1), .alu .cmp .eax (.imm 0)]
def factorStep (n : Nat) : Prog isa :=
  .seq (.block (shiftExponent (2 * n) (slot n 8))) (.block (factorTest n))
def factor (n : Nat) : Prog isa :=
  .seq (.block factorInit)
    (.seq (.loop (factorStep n) .e) (.block [.store (sc primeTwos) .ebx]))
end VG.Impl.Dsa.X86.Generation
