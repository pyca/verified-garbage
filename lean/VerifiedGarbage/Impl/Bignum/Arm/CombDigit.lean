module

public import VerifiedGarbage.TCB.Arm.Isa
public import VerifiedGarbage.TCB.Code

/-! Five public exponent positions form one secret comb digit. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm.CombDigit
open VG VG.Arm

/-- Shift a secret byte by a public, nonzero count in r2. -/
def shift : Prog isa :=
  .loop (.block [.mov .r11 (.shifted .r11 .lsr 1), .subs .r2 .r2 (.imm 1)]) .ne

/-- r9 is a public bit index; r4 the big-endian byte buffer and r5 its length. -/
def load : List Instr :=
  [.mov .r12 (.shifted .r9 .lsr 3), .dp .sub .r12 .r5 (.reg .r12),
   .dp .sub .r12 .r12 (.imm 1), .dp .add .r12 .r4 (.reg .r12),
   .ldrb .r11 .r12 0, .dp .and .r2 .r9 (.imm 7), .cmp .r2 (.imm 0)]

/-- Above the public width N in r8, the bit is zero without reading memory. -/
def bit : Prog isa :=
  .seq (.block [.dp .sub .r12 .r9 (.reg .r8),
    .mov .r12 (.shifted .r12 .lsr 31), .cmp .r12 (.imm 0)])
    (.ite .ne (.seq (.block load)
      (.seq (.ite .ne shift (.block [])) (.block [.dp .and .r11 .r11 (.imm 1)])))
      (.block [.mov .r11 (.imm 0)]))

def tooth (j : Nat) : Prog isa :=
  .seq bit (.block [.dp .orr .r10 .r10 (if j=0 then .reg .r11 else .shifted .r11 .lsl j), .dp .add .r9 .r9 (.reg .r7)])

/-- r6=i, r7=d, r8=N; return the five-tooth digit in r11. -/
def code : Prog isa :=
  .seq (.block [.mov .r9 (.reg .r6), .mov .r10 (.imm 0)])
    (.seq (tooth 0) (.seq (tooth 1) (.seq (tooth 2) (.seq (tooth 3)
      (.seq (tooth 4) (.block [.mov .r11 (.reg .r10)]))))))

end VG.Impl.Bignum.Arm.CombDigit
