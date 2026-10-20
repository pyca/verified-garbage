module

public import VerifiedGarbage.Impl.Bignum.Arm.Row

/-! A multiply-add row writes each word one place below its old accumulator.
The complete scalar and public pointers survive. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.DownRow
open VG VG.Arm VG.Impl.Bignum.Arm

def step : Prog isa :=
  .seq (.block [.ldr .r2 .r12 0]) (.seq (.block rowProduct)
    (.seq (.block [.ldr .r5 .r0 4])
      (.seq (.block (addWord .r5 ++ addCarry)) (.block [.str .r3 .r0 0]))))

def body : Prog isa := .seq step (.block rowAdvance)

def loop : Prog isa := .loop body .ne

def code : Prog isa := .seq (.block rowSplit) (.seq loop (.block rowJoin))

end VG.Impl.Bignum.Arm.DownRow
