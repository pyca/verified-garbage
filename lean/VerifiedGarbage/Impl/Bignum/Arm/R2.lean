module

public import VerifiedGarbage.Impl.Bignum.Arm.SetSmallFn
public import VerifiedGarbage.Impl.Bignum.Arm.DoubleLoop
public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! # RSA Montgomery R-squared precomputation

Initialize array 4 to one, array 7 to two, then perform `65 w` modular
doublings, which leave `2^(65 w) mod m` in array 4, for the shared radix
`R = 2^(64 w)`. Six Montgomery squarings of array 4 in place then take
`2^(64 w + k)` to `2^(64 w + 2 k)` each (`x ↦ x² R⁻¹`), from `k = w` to
`k = 64 w`: `R² mod m`. All loop bounds are public.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def smallConstArgs (o value : BitVec 32) : List Instr := [.mov .r2 (.imm o), .mov .r5 (.imm value)]

def smallConst (o value : BitVec 32) : Prog isa := .seq (.block (smallConstArgs o value)) setSmallFn

def r2Constants : Prog isa := .seq (smallConst 4 1) (smallConst 7 2)

/-- The count of doublings, `65 w = w + 64 w`, at header byte 208. -/
def r2CountInit : List Instr :=
  [.ldr .r1 .r0 48, .dp .add .r1 .r1 (.shifted .r1 .lsl 6), .str .r1 .r0 208]

def r2Init : Prog isa := .seq r2Constants (.block r2CountInit)

/-- Six squarings of array 4 in place. -/
def r2Squares : Prog isa :=
  .seq (squareOp 4 4) (.seq (squareOp 4 4) (.seq (squareOp 4 4)
    (.seq (squareOp 4 4) (.seq (squareOp 4 4) (squareOp 4 4)))))

def r2 : Prog isa := .seq r2Init (.seq doubleLoop r2Squares)

end VG.Impl.Bignum.Arm
