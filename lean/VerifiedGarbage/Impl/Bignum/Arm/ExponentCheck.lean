module

public import VerifiedGarbage.TCB.Arm.Isa

/-! # Validate a public RSA exponent using native 32-bit registers

r1 points to a nonempty exponent and lr is its byte length. r3 holds the
low 32 bits; r4 holds the upper bits saturated at 2. Saturation branches
only on the public exponent. No input or private-key bytes are accessed.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def exponentAccumulate : List Instr :=
  [.ldrb .r7 .r1 0, .mov .r5 (.shifted .r3 .lsr 24),
   .mov .r4 (.shifted .r4 .lsl 8), .dp .add .r4 .r4 (.reg .r5),
   .mov .r3 (.shifted .r3 .lsl 8), .dp .add .r3 .r3 (.reg .r7),
   .mov .r5 (.shifted .r4 .lsr 1), .subs .r5 .r5 (.imm 0)]

def exponentAdvance : List Instr :=
  [.dp .add .r1 .r1 (.imm 1), .subs .lr .lr (.imm 1)]

def exponentConsume : Prog isa :=
  .seq (.block exponentAccumulate) (.ite .eq (.block []) (.block [.mov .r4 (.imm 2)]))

def exponentByte : Prog isa := .seq exponentConsume (.block exponentAdvance)

def exponentScan : Prog isa :=
  .seq (.block [.mov .r3 (.imm 0), .mov .r4 (.imm 0)]) (.loop exponentByte .ne)

def exponentBoundsTest : List Instr :=
  [.mov .r5 (.shifted .r4 .lsr 1), .dp .and .r7 .r3 (.imm 1),
   .dp .eor .r7 .r7 (.imm 1), .dp .orr .r5 .r5 (.reg .r7), .subs .r5 .r5 (.imm 0)]

def exponentOneTest : List Instr :=
  [.dp .eor .r5 .r3 (.imm 1), .dp .orr .r5 .r5 (.reg .r4), .subs .r5 .r5 (.imm 0)]

def exponentResult (b : Bool) : Prog isa := .block [.mov .r7 (.imm (BitVec.ofNat 32 b.toNat))]

def exponentTest : Prog isa :=
  .seq (.block exponentBoundsTest)
    (.ite .eq
      (.seq (.block exponentOneTest) (.ite .eq (exponentResult false) (exponentResult true)))
      (exponentResult false))

def exponentCheck : Prog isa := .seq exponentScan exponentTest

end VG.Impl.Bignum.Arm
