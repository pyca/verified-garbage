module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxRotate8

/-! Register-resident rectangular products for the raw multiplication kernel. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxRect8
open VG.X86_64

def carryOffset : Nat := 8 * sFn 14

def upper : List Instr :=
  [.mov .rdx (.mem (hdr (sFn 14))), .alu .add .rsi (.imm 64)]

/-- Address a tile using the two public word indices, which its caller leaves
in `rax` and `rdx` as well as in slots 28 and 29 (not reloaded: it has just
stored them). -/
def setup (a b : Nat) : List Instr :=
  [.shift .shl .rax 3,
   .mov .rcx (.mem (hdr (sArr a))), .alu .add .rcx (.reg .rax),
   .shift .shl .rdx 3,
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

/-! ## A row of a square, with the carry of the row before

A square's rows, from the lowest, each leave their top carry in `sFn 15`
(`hand`) instead of propagating it through the words above, which other
rows and blocks have written; the next row, whose last input block starts at
that carry's word, adds it to its pending carry before that block. -/

/-- The slot of the carry handed from a row to the next. -/
def handOffset : Nat := 8 * sFn 15

/-- The column index up to the next block, ZF set when that block is the last. -/
def nextColumnS : List Instr :=
  [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8),
   .store (hdr (sFn 13)) .rax, .alu .add .rax (.imm 8), .alu .cmp .rax (.mem (hdr sW))]

def rowStepS : Prog isa :=
  .seq streamTile (.block nextColumnS)

/-- ZF set when the row has one block. -/
def oneTest : List Instr :=
  [.mov .rax (.mem (hdr (sFn 13))), .alu .add .rax (.imm 8), .alu .cmp .rax (.mem (hdr sW))]

/-- The handed carry added to the pending carry (its slot is left as it is:
the next row's tail overwrites it, and the last row's is not read again). -/
def addHand : List Instr :=
  [.mov .rax (.mem (hdr (sFn 15))), .alu .add .rax (.mem (hdr (sFn 14))), .store (hdr (sFn 14)) .rax]

/-- `row`, with the handed carry added before the last block. -/
def rowS (a b : Nat) : Prog isa :=
  .seq (.block (setup a b)) (.seq (.block AdxRotate8.loadCols)
    (.seq (.seq (.block oneTest) (.ite .e (.block []) (.loop rowStepS .ne)))
      (.seq (.block addHand) (.seq rowStep (.block AdxRotate8.storeCols)))))

end VG.Impl.Bignum.X86_64.AdxRect8
