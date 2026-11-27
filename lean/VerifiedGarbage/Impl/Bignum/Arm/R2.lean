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

/-- The count of squarings, six, at header byte 208, which the doublings
leave zero. -/
def r2SquareCount : List Instr := [.mov .r1 (.imm 6), .str .r1 .r0 208]

/-- A squaring of array 4 in place, then the count down (`doubleCount`). -/
def r2SquareStep : Prog isa := .seq (squareOp 4 4) (.block doubleCount)

/-- Six squarings of array 4 in place, in a loop over the count. -/
def r2Squares : Prog isa := .seq (.block r2SquareCount) (.loop r2SquareStep .ne)

def r2 : Prog isa := .seq r2Init (.seq doubleLoop r2Squares)

/-! The same with the squarings `op 4 4 4`, any Montgomery product's (a call
of a shared one, `MontCall.op`). -/

def r2SquareStepWith (op : Nat → Nat → Nat → Prog isa) : Prog isa := .seq (op 4 4 4) (.block doubleCount)
def r2SquaresWith (op : Nat → Nat → Nat → Prog isa) : Prog isa :=
  .seq (.block r2SquareCount) (.loop (r2SquareStepWith op) .ne)
def r2With (op : Nat → Nat → Nat → Prog isa) : Prog isa := .seq r2Init (.seq doubleLoop (r2SquaresWith op))

end VG.Impl.Bignum.Arm
