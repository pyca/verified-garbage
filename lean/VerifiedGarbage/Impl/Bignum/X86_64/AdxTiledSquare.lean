module

public import VerifiedGarbage.Impl.Bignum.X86_64.Fill
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct

/-! Triangular block squares combined with rectangular cross-block rows. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxTiledSquare
open VG.X86_64

/-- A row's start, from its index in `rax`: the column index one block above
it into `rdx` and slot 29, a zero carry into slot 30. -/
def rowInit : List Instr :=
  [.mov .rdx (.reg .rax),.alu .add .rdx (.imm 8),.store (hdr (sFn 13)) .rdx,
   .mov32 .rcx (.imm 0),.store (hdr (sFn 14)) .rcx]

def nextRow : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 12)) .rax,
   .mov .rcx (.mem (hdr sW)),.alu .sub .rcx (.imm 8),.alu .cmp .rax (.reg .rcx)]

/-- ZF set for the last row. -/
def lastTest : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 16),.alu .cmp .rax (.mem (hdr sW))]

/-- The row's carry: through the words above for the last row, handed to the
next row otherwise. -/
def tail : Prog isa := .seq (.block lastTest)
  (.ite .e AdxTiledProduct.tail (.block [.mov .rax (.mem (hdr (sFn 14))),.store (hdr (sFn 15)) .rax]))

def row (a : Nat) : Prog isa := .seq (.block rowInit)
  (.seq (AdxRect8.rowS a a) (.seq tail (.block nextRow)))

/-- The rows, then `tileFill 1 2` for the 18 bytes their counters' registers
saved. -/
def rows (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax,.store (hdr (sFn 15)) .rax])
    (.seq (.loop (row a) .ne) (.block (tileFill 1 2)))

/-- A row of a square of one row (16 words), which has no carry to hand on:
its carry through the words above. -/
def row1 (a : Nat) : Prog isa := .seq (.block rowInit)
  (.seq (AdxRect8.row a a) (.seq AdxTiledProduct.tail (.block nextRow)))

/-- As `rows`, with `tileFill 1 2` for the same 18 bytes. -/
def rows1 (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax])
    (.seq (.loop (row1 a) .ne) (.block (tileFill 1 2)))

/-- No rows for 8 words, the row without hand-off for 16, the rows with it
otherwise. -/
def rowsChoice (a : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 16)]) (.ite .e (rows1 a) (rows a))))

def rawCross (a : Nat) : Prog isa := .seq (.block (Adx.setup a))
  (.seq AdxHeader.save (.seq (.seq (AdxTri8.blocks a)
    (rowsChoice a)) AdxHeader.restore))

/-- `rawCross` for a caller that keeps the borrowed header words itself: the
high pad is only cleared. -/
def rawCrossBare (a : Nat) : Prog isa := .seq (.block (Adx.setup a))
  (.seq (.seq (AdxTri8.blocks a) (rowsChoice a)) AdxHeader.clear)

/-- The diagonal, in groups of eight: the tiles' sizes are multiples of 8. -/
def diagonal (a : Nat) : Prog isa :=
  .seq (.block (Adx.setup a)) (.seq (.block [.mov .r10 (.reg .rbx)]) AdxSquareGrouped.diagonal8)

def rawSquare (a : Nat) : Prog isa := .seq (rawCross a) (diagonal a)

def rawSquareBare (a : Nat) : Prog isa := .seq (rawCrossBare a) (diagonal a)

def montSquare (o a : Nat) : Prog isa := .seq (rawSquare a) (AdxTiledProduct.redcFinish o)

end VG.Impl.Bignum.X86_64.AdxTiledSquare
