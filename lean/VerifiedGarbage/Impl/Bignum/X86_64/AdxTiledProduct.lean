import VerifiedGarbage.Impl.Bignum.X86_64.AdxHeader
import VerifiedGarbage.Impl.Bignum.X86_64.AdxCarry8
import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare
import VerifiedGarbage.Impl.Bignum.X86_64.AdxFinish8

/-! Full raw multiplication from eight-word rectangular rows. -/
namespace VG.Impl.Bignum.X86_64.AdxTiledProduct
open VG.X86_64

def tailTest : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8), .alu .cmp .rax (.mem (hdr sW))]

def tailSetup : List Instr :=
  [.mov .rbp (.mem (hdr (sFn 14))), .alu .add .rsi (.imm 64),
   .mov .rdx (.mem (hdr sW)), .shift .shl .rdx 4,
   .alu .add .rdx (.mem (hdr (sArr Public.aAcc))), .alu .add .rdx (.imm 16), .mov32 .rcx (.imm 0)]

def tail : Prog isa := .seq (.block tailTest)
  (.ite .e (.block []) (.seq (.block tailSetup) AdxCarry8.propagate))

def rowInit : List Instr :=
  [.mov32 .rax (.imm 0), .store (hdr (sFn 14)) .rax, .store (hdr (sFn 13)) .rax]

def nextRow : List Instr :=
  [.mov .rax (.mem (hdr (sFn 12))), .alu .add .rax (.imm 8),
   .store (hdr (sFn 12)) .rax, .alu .cmp .rax (.mem (hdr sW))]

def row (a b : Nat) : Prog isa := .seq (.block rowInit)
  (.seq (AdxRect8.row a b) (.seq tail (.block nextRow)))

def rows (a b : Nat) : Prog isa :=
  .seq (.block [.mov32 .rax (.imm 0),.store (hdr (sFn 12)) .rax]) (.loop (row a b) .ne)

/-- The borrowed header is saved only after the scratch window is cleared. -/
def rawProduct (a b : Nat) : Prog isa :=
  .seq (.block (Adx.setup b)) (.seq Adx.zeroWin8
    (.seq AdxHeader.save (.seq (rows a b) AdxHeader.restore)))

def montMul (o a b : Nat) : Prog isa :=
  .seq (rawProduct a b) (.seq AdxRotate8.redc
    (.seq (.block [.mov .r10 (.mem (hdr (sArr Public.aN)))]) (Adx.finish8 o)))

def alignedChoice (o a b : Nat) : Prog isa :=
  .seq (.block AdxSquare.redcTest) (.ite .e (montMul o a b) (Adx.montMulAdx o a b))

def choice (o a b : Nat) : Prog isa :=
  .seq (.block Adx.sizeTest) (.ite .e (alignedChoice o a b) (Adx.montMulAdx o a b))

/-- Keep the specialized square while using rectangular tiles for products. -/
def dispatch (o a b : Nat) : Prog isa :=
  if a=b then AdxSquare.montMul o a b else choice o a b

end VG.Impl.Bignum.X86_64.AdxTiledProduct
