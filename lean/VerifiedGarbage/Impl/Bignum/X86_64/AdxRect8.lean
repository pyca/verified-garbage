import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Register-resident rectangular products for the raw multiplication kernel. -/
namespace VG.Impl.Bignum.X86_64.AdxRect8
open VG.X86_64

def carryOffset : Nat := 8 * sFn 14

def upper : List Instr :=
  [.mov .rdx (.mem (hdr (sFn 14))), .alu .add .rsi (.imm 64)]

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

/-- A tile whose upper words stay in the columns: the eight products, then the
next eight output words and the carry added to the columns, which the next
tile continues from, so that no tile stores its columns and reloads them. -/
def streamTile : Prog isa :=
  .seq (AdxRotate8.productN 8) (.seq (.block upper)
    (.seq (.block AdxDualAdd.addInput) (.block [.store (hdr (sFn 14)) .rax, .alu .add .rbp (.imm 64)])))

def rowStep : Prog isa :=
  .seq streamTile (.block nextColumn)

/-- Process the remaining column blocks of a row, the columns loaded once at
its start and stored once at its end; the caller supplies its starting public
column index and a zero pending carry. -/
def row (a b : Nat) : Prog isa :=
  .seq (.block (setup a b)) (.seq (.block AdxRotate8.loadCols)
    (.seq (.loop rowStep .ne) (.block AdxRotate8.storeCols)))

end VG.Impl.Bignum.X86_64.AdxRect8
