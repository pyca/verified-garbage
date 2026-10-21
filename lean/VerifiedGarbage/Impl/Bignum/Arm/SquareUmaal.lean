module

public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! The shared square uses UMAAL for each diagonal multiply-accumulate. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def macU : List Instr :=
  [.mov .r3 (.reg .r10), .mov .r4 (.reg .r11), .umaal .r3 .r4 .r1 .r2]

def diagStepU : Prog isa :=
  .seq (.block [.ldr .r1 .r12 0, .mov .r2 (.reg .r1), .ldr .r10 .r0 0])
    (.seq (.block macU) (.block [.str .r3 .r0 0, .ldr .r10 .r0 4, .adds .r4 .r4 (.reg .r10),
      .mov .r11 (.imm 0), .adc .r11 .r11 (.imm 0), .str .r4 .r0 4]))

def diagLoopU : Prog isa := .loop (.seq diagStepU (.block diagAdvance)) .ne

def sqDiagU : Prog isa := .seq sqAnchor (.seq (.block sqDiagArgs) diagLoopU)

def sqBodyU : Prog isa :=
  .seq sqInit (.seq crossRows (.seq sqDouble (.seq sqDiagU (.seq sqReduce sqFinish))))

def squareBodyU : Prog isa := .seq (.block MontFn.bases) sqBodyU

end VG.Impl.Bignum.Arm
