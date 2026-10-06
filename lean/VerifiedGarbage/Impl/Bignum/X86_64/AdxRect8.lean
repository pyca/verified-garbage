import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Register-resident rectangular products for the raw multiplication kernel. -/
namespace VG.Impl.Bignum.X86_64.AdxRect8
open VG.X86_64

/-- Add the upper output block and incoming word carry to the eight columns,
then store them. The outgoing carry is in `rax`. -/
def finish : Prog isa :=
  .seq (.block AdxDualAdd.addInput) (.block AdxRotate8.storeCols)

/-- Consume eight words from each input, leaving eight low output words in
memory and eight high words in registers. -/
def product : Prog isa :=
  .seq (.block AdxRotate8.loadCols) (AdxRotate8.productN 8)

def carryOffset : Nat := 8 * sFn 14

def upper : List Instr :=
  [.mov .rdx (.mem (hdr (sFn 14))), .alu .add .rsi (.imm 64)]

/-- Accumulate one 8-by-8 product. The row carry is kept in header slot 30;
the enclosing raw kernel saves and restores that slot. -/
def tile : Prog isa :=
  .seq product (.seq (.block upper) (.seq finish
    (.block [.store (hdr (sFn 14)) .rax])))

/-- Address a tile using the two public word indices in slots 28 and 29. -/
def setup (a b : Nat) : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))), .shift .shl .rax 3,
   .mov .rcx (.mem (hdr (sArr a))), .alu .add .rcx (.reg .rax),
   .mov .rdx (.mem (hdr (sFn 13))), .shift .shl .rdx 3,
   .mov .rbp (.mem (hdr (sArr b))), .alu .add .rbp (.reg .rdx),
   .alu .add .rax (.reg .rdx), .mov .rsi (.mem (hdr (sArr Public.aAcc))),
   .alu .add .rsi (.reg .rax), .alu .add .rsi (.imm 16)]

def nextColumn : List Instr :=
  [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
   .store (hdr (sFn 13)) .rax, .alu .cmp .rax (.mem (hdr sW))]

end VG.Impl.Bignum.X86_64.AdxRect8
