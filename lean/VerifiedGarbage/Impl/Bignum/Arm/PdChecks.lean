module

public import VerifiedGarbage.Impl.Bignum.Arm.ArrayCompare
public import VerifiedGarbage.Impl.Bignum.Arm.R2
public import VerifiedGarbage.Impl.Bignum.Arm.SaveAcceptance
public import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance

/-! # Public sanity checks on packed RSA precomputations

Require N > 1, R² < N, and odd N before Montgomery arithmetic. These
checks concern only the public key; the input has not been imported yet.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def pdOddRead : Prog isa := .seq (.block [.ldr .r1 .r0 64])
  (.seq (.block [.ldrb .r1 .r1 0]) (.block [.ldrSp .r11 48]))
def pdOddFinish : List Instr :=
  [.dp .and .r1 .r1 (.imm 1), .dp .and .r11 .r11 (.reg .r1), .subs .r11 .r11 (.imm 0)]
def pdOdd : Prog isa := .seq pdOddRead (.block pdOddFinish)
def pdChecks : Prog isa := .seq (smallConst 7 1)
  (.seq (arrayCompare 7 0) (.seq (.block saveAcceptance)
    (.seq (arrayCompare 4 0) (.seq (.block mergeAcceptance) pdOdd))))

end VG.Impl.Bignum.Arm
