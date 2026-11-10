module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
public import VerifiedGarbage.Impl.Bignum.Arm.ExportBufferMasked
public import VerifiedGarbage.Impl.Bignum.Arm.SubModArray

/-! # ARMv7 private RSA CRT pipeline

The 56-byte frame retains the public lengths and argument pointers. After
importing n, slot 8 holds the main workspace; slot 0 follows the active
workspace. The only conditional branch validates the public modulus.
All secret validation bits accumulate at slot 48 and mask the final output.
Each factor's power runs in the narrow workspace at the factor's own width.
-/

@[expose] public section

namespace VG.Impl.Bignum.Arm.CrtFn
open VG VG.Arm VG.Impl.Bignum.Arm.Crt

def entry : List Instr :=
  [.addSp .r12 0, .str .r0 .r12 4, .ldrSp .r0 104, .str .r0 .r12 0,
   .mov .r4 (.reg .r2), .mov .r6 (.reg .r3)]

def acceptInput : Prog isa :=
  .seq (savedOperand 1 56 12) (.seq inputCompare (.block saveAcceptance))
def loadPBody : Prog isa := .seq (savedOperand 0 64 68) (.seq (savedOperand 1 96 100)
  (.seq inputCompare (.block mergeAcceptance)))
def loadP : Prog isa := .seq (selectChild 224) (.seq loadPBody selectMain)
def loadQ : Prog isa := .seq (selectChild 228) (.seq (savedOperand 0 72 76) selectMain)
def validate : Prog isa :=
  .seq acceptInput (.seq loadP (.seq loadQ (.seq validateProduct (.block mergeAcceptance))))

def powerWith (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq (selectChild slot) (.seq (narrowPowerWith phase slot primeSlot exponentSlot) selectMain)
def qSource : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 228]
def coefficientPhase : Prog isa := .seq (selectChild 224)
  (.seq (.block qSource) (.seq (transferArray 1 6) (.seq coefficient selectMain)))
def outputArgs : List Instr := [.ldr .r1 .r0 232, .ldrSp .r4 4, .ldrSp .r6 12]
def finish : Prog isa := .seq (.block qSource) (.seq (transferArray 1 6)
  (.seq recombine (.seq (.block outputArgs) exportBufferMasked)))
def computeWith (phase : Prog isa) : Prog isa := .seq (powerWith phase 224 64 80)
  (.seq (powerWith phase 228 72 88) (.seq coefficientPhase finish))

/-! ## Each factor at its own width only (prototype) -/

/-- Copy `w_p` words from `r1` on into the narrow array at header byte `slot`. -/
def copyInto (slot : Nat) : Prog isa :=
  .seq (.block [.ldr .r4 .r0 slot, .ldr .lr .r0 48, .mov .lr (.shifted .lr .lsl 3), .mov .r5 (.reg .r0),
    .mov .r0 (.reg .r4)]) (.seq copyBytes (.block [.mov .r0 (.reg .r5)]))
/-- The low `w_p` words of the source into array 5, the next `w_p` into array 1. -/
def splitInto (src : List Instr) : Prog isa :=
  .seq (clearOperandBuffer 104) (.seq (clearOperandBuffer 72) (.seq (.block src) (.seq (copyInto 104) (copyInto 72))))
def splitSwap (src : List Instr) : Prog isa :=
  .seq (clearOperandBuffer 104) (.seq (clearOperandBuffer 72) (.seq (.block src) (.seq (copyInto 72) (copyInto 104))))
/-- Array 1 `:=` `l + h R mod p`, for `l` in array 5 and `h` in array 1. -/
def reduceSplit : Prog isa :=
  .seq (montOp 5 5 4) (.seq (montOp 5 5 7) (.seq (montOp 1 1 4)
    (.seq (clearOperandBuffer 88) (.seq (subModArray 2 3 1) (subModArray 1 5 2)))))
/-- The narrow workspace's address in `r1`, `r0` kept. -/
def narrowAddress0 : List Instr :=
  [.ldrSp .r2 8, .ldr .r1 .r2 240, .ldr .r2 .r2 48, .mov .r2 (.shifted .r2 .lsl 4),
   .dp .add .r2 .r2 (.imm 8), .dp .add .r1 .r1 (.reg .r2)]
def narrowPowerHalf (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq (savedOperand 1 56 12) (.seq (clearOperandBuffer 112) (.seq (enterNarrow (primeSlot + 4)) (.seq (narrowPrime primeSlot)
    (.seq (smallConst 7 1) (.seq (splitInto (narrowSource slot)) (.seq reduceSplit
    (.seq (narrowExpWith phase exponentSlot) (narrowResult slot))))))))
def powerHalf (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq (selectChild slot) (.seq (narrowPowerHalf phase slot primeSlot exponentSlot) selectMain)
def reenterNarrow : Prog isa := .seq (.block narrowAddress) (.block activateWorkspace)
def mqSource : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 228, .ldr .r1 .r1 112]
def coefficientHalf : Prog isa :=
  .seq reenterNarrow (.seq (splitInto mqSource) (.seq reduceSplit (.seq (subModArray 5 6 1)
    (.seq (savedOperand 1 96 100) (.seq (montOp 1 1 4) (.seq (montOp 5 5 1)
    (.seq (.block [.ldrSp .r0 8, .ldr .r0 .r0 224]) (.seq (.block activateWorkspace)
    (.seq (clearOperandBuffer 104) (.seq (.block narrowAddress0) (.seq (transferArray 5 5) selectMain)))))))))))
def computeHalf (phase : Prog isa) : Prog isa := .seq (powerHalf phase 228 72 88)
  (.seq (powerHalf phase 224 64 80) (.seq coefficientHalf finish))

def prepare : Prog isa := .seq (.block PcFn.head) (.seq setupAll
  (.seq (savedOperand 0 8 12) (.block saveMain)))
def validWith (phase : Prog isa) : Prog isa := .seq prepare (.seq validate (computeHalf phase))
def bodyWith (phase : Prog isa) : Prog isa := .seq (.block modulusCheck) (.ite .eq (validWith phase) PublicFn.fail)
def codeWith (phase : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq (bodyWith phase) (.block PcFn.restore))) (.pop .r12 56)

def code : Prog isa := codeWith windowExpPhase

end VG.Impl.Bignum.Arm.CrtFn
