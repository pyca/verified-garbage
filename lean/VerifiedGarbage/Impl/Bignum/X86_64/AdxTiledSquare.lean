module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
public import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct

/-! Triangular block squares combined with rectangular cross-block rows. -/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.AdxTiledSquare
open VG.X86_64

def rowInit : List Instr :=
  [.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax,
   .mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax]

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

def rows (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax,.store (hdr (sFn 15)) .rax]) (.loop (row a) .ne)

/-! ## The cross tile of a 16-word square

A square of 16 words has one cross tile, `a[0..8) * a[8..16)`, at words 8
to 24 of the raw product, with nothing pending before it: the tile's
columns take the next eight words in one carry chain from a clear CF, and
the chain's carry runs through the eight words above. -/

/-- The tile's row and column indices for `AdxRect8.setup`. -/
def init16 : List Instr :=
  [.mov32 .rax (.imm 0), .store (hdr (sFn 12)) .rax, .mov32 .rax (.imm 8), .store (hdr (sFn 13)) .rax]

/-- The words above the tile's low words added to its columns and stored,
the carry into `rbp`; `rsi` to the eight words above them and `rcx` zero,
for `AdxCarry8.block8`. -/
def mid16 : List Instr :=
  ([.alu .add .rsi (.imm 64), .alu32 .xor .rax (.reg .rax)] : List Instr) ++ AdxRotate8.addChainC ++
    AdxCarry8.close ++ AdxRotate8.storeCols ++ ([.alu .add .rsi (.imm 64), .mov32 .rcx (.imm 0)] : List Instr)

def cross16 (a : Nat) : Prog isa :=
  .seq (.block init16) (.seq (.block (AdxRect8.setup a a)) (.seq (.block AdxRotate8.loadCols)
    (.seq (AdxRotate8.productN 8) (.seq (.block mid16) AdxCarry8.block8))))

/-- No rows for 8 words, the one cross tile for 16, the rows with hand-off
otherwise. -/
def rowsChoice (a : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)])
    (.ite .e (.block [])
      (.seq (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 16)]) (.ite .e (cross16 a) (rows a))))

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
