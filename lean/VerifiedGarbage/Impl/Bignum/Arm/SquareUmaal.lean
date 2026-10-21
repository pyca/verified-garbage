module

public import VerifiedGarbage.Impl.Bignum.Arm.Square

/-! The shared square fuses cross-product doubling with each UMAAL diagonal product. -/

@[expose] public section
namespace VG.Impl.Bignum.Arm
open VG VG.Arm

def macU : List Instr :=
  [.mov .r3 (.reg .r10), .mov .r4 (.reg .r11), .umaal .r3 .r4 .r1 .r2]

/-- Double the cross-product pair, retaining its bit above the pair. -/
def fusedDiagHead : List Instr :=
  [.ldr .r1 .r12 0, .ldr .r10 .r0 0, .ldr .r5 .r0 4,
   .mov .r6 (.shifted .r5 .lsr 31), .adds .r10 .r10 (.reg .r10), .adc .r5 .r5 (.reg .r5)]

def squareMacU : List Instr :=
  [.mov .r3 (.reg .r10), .mov .r4 (.reg .r11), .umaal .r3 .r4 .r1 .r1]

def fusedDiagTail : List Instr :=
  [.adds .r4 .r4 (.reg .r5), .adc .r11 .r6 (.imm 0), .str .r3 .r0 0, .str .r4 .r0 4]

def diagStepU : Prog isa :=
  .seq (.block fusedDiagHead) (.seq (.block squareMacU) (.block fusedDiagTail))

def diagLoopU : Prog isa := .loop (.seq diagStepU (.block diagAdvance)) .ne

def sqDiagU : Prog isa := .seq sqAnchor (.seq (.block sqDiagArgs) diagLoopU)

def sqBodyU : Prog isa :=
  .seq sqInit (.seq crossRows (.seq sqDiagU (.seq sqReduce sqFinish)))

def squareBodyU : Prog isa := .seq (.block MontFn.bases) sqBodyU

end VG.Impl.Bignum.Arm
