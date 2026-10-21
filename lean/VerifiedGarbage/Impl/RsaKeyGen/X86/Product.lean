module

public import VerifiedGarbage.Impl.Mont.X86.Dynamic

/-! # Native word products for RSA key assembly

The product uses the paired multiply-accumulate loop from the x86
Montgomery implementation, without Montgomery reduction. EDI is the
workspace base; EBP advances over the first operand and the product.
The two operand widths are public. Only the second width must be even.
The destination has `left + right + 2` words, including carry space.
ESI is preserved for enclosing arithmetic schedules.
-/

@[expose] public section
namespace VG.Impl.RsaKeyGen.X86.Product
open VG VG.X86 VG.Impl.Mont.X86 VG.Impl.Mont.X86.Dynamic

/-- Save the current word of the first operand for the paired inner loop. -/
def load (a mult : Nat) : List Instr :=
  [.mov .eax (.mem (at_ .ebp a)), .store (sc mult) .eax]

/-- Accumulate one word times the second operand, retaining EBP. -/
def accumulate (right out a b mult : Nat) : Prog isa :=
  .seq (.block (load a mult)) (mulRowW out b right mult)

/-- Advance the product window and test the public first-operand bound. -/
def advance (left : Nat) : List Instr :=
  [.alu .add .ebp (.imm 4), .mov .edx (.reg .edi),
    .alu .add .edx (.imm (BitVec.ofNat 32 (4 * left))), .alu .cmp .ebp (.reg .edx)]

def row (left right out a b mult : Nat) : Prog isa :=
  .seq (accumulate right out a b mult) (.block (advance left))

/-- Schoolbook multiplication, with public loops over both operands.
The destination and multiplier slot must be disjoint from the operands. -/
def code (left right out a b mult : Nat) : Prog isa :=
  .seq (zerosW out (left + right + 2))
    (.seq (.block [.mov .ebp (.reg .edi)])
      (.loop (row left right out a b mult) .ne))

end VG.Impl.RsaKeyGen.X86.Product
