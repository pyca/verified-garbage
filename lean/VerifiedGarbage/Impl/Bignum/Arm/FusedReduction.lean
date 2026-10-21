module

public import VerifiedGarbage.Impl.Bignum.Arm.DownRow

/-! Montgomery cancellation writes the quotient while producing each row.
The known-zero low word is discarded; no separate accumulator shift runs. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.FusedReduction
open VG VG.Arm VG.Impl.Bignum.Arm

def firstArgs : List Instr := [.ldr .r2 .r12 0, .ldr .r10 .r0 0]

def firstNext : List Instr :=
  [.mov .r11 (.reg .r4), .dp .add .r12 .r12 (.imm 4), .subs .lr .lr (.imm 1)]

def first : Prog isa := .seq (.block firstArgs) (.seq (.block mac) (.block firstNext))

/-- The two high accumulator words and the row carry, stored one word down. -/
def top : Prog isa :=
  .seq (.block [.ldr .r3 .r0 4, .ldr .r4 .r0 8])
    (.seq (.block (addWord .r11))
      (.block [.str .r3 .r0 0, .str .r4 .r0 4, .dp .add .r0 .r0 (.imm 8)]))

def code : Prog isa := .seq first (.seq DownRow.code top)

end VG.Impl.Bignum.Arm.FusedReduction
