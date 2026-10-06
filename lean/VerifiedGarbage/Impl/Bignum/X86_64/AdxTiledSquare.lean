import VerifiedGarbage.Impl.Bignum.X86_64.AdxTri8
import VerifiedGarbage.Impl.Bignum.X86_64.AdxTiledProduct

/-! Triangular block squares combined with rectangular cross-block rows. -/
namespace VG.Impl.Bignum.X86_64.AdxTiledSquare
open VG.X86_64

def rowInit : List Instr :=
  [.mov32 .rax (.imm 0),.store (hdr (sFn 14)) .rax,
   .mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 13)) .rax]

def nextRow : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))),.alu .add .rax (.imm 8),.store (hdr (sFn 12)) .rax,
   .mov .rcx (.mem (hdr sW)),.alu .sub .rcx (.imm 8),.alu .cmp .rax (.reg .rcx)]

def row (a : Nat) : Prog isa := .seq (.block rowInit)
  (.seq (AdxRect8.row a a) (.seq AdxTiledProduct.tail (.block nextRow)))

def rows (a : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) (.loop (row a) .ne)

def rowsChoice (a : Nat) : Prog isa :=
  .seq (.block [.mov .rax (.mem (hdr sW)),.alu .cmp .rax (.imm 8)])
    (.ite .e (.block []) (rows a))

def rawCross (a : Nat) : Prog isa := .seq (.block (Adx.setup a))
  (.seq Adx.zeroWin (.seq AdxHeader.save (.seq (.seq (AdxTri8.blocks a)
    (rowsChoice a)) AdxHeader.restore)))

def rawSquare (a : Nat) : Prog isa := .seq (rawCross a)
  (.seq (.block (Adx.setup a)) (.seq (.block [.mov .r10 (.reg .rbx)]) AdxSquare.diagonalChoice))

def montSquare (o a : Nat) : Prog isa := .seq (rawSquare a)
  (.seq AdxRotate8.redc (.seq (.block [.mov .r10 (.mem (hdr (sArr Public.aN)))]) (Adx.finish o)))

end VG.Impl.Bignum.X86_64.AdxTiledSquare
