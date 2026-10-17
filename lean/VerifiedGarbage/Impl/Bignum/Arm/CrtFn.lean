module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
public import VerifiedGarbage.Impl.Bignum.Arm.SavedOperand
public import VerifiedGarbage.Impl.Bignum.Arm.MergeAcceptance
public import VerifiedGarbage.Impl.Bignum.Arm.CrtValidateProduct
public import VerifiedGarbage.Impl.Bignum.Arm.CrtNarrowPower
public import VerifiedGarbage.Impl.Bignum.Arm.CrtCoefficient
public import VerifiedGarbage.Impl.Bignum.Arm.TransferArray
public import VerifiedGarbage.Impl.Bignum.Arm.CrtRecombine
public import VerifiedGarbage.Impl.Bignum.Arm.ExportBufferMasked

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

def power (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq (selectChild slot) (.seq (narrowPower slot primeSlot exponentSlot) selectMain)
def qSource : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 228]
def coefficientPhase : Prog isa := .seq (selectChild 224)
  (.seq (.block qSource) (.seq (transferArray 1 6) (.seq coefficient selectMain)))
def outputArgs : List Instr := [.ldr .r1 .r0 232, .ldrSp .r4 4, .ldrSp .r6 12]
def finish : Prog isa := .seq (.block qSource) (.seq (transferArray 1 6)
  (.seq recombine (.seq (.block outputArgs) exportBufferMasked)))
def compute : Prog isa := .seq (power 224 64 80)
  (.seq (power 228 72 88) (.seq coefficientPhase finish))

def prepare : Prog isa := .seq (.block PcFn.head) (.seq setupAll
  (.seq (savedOperand 0 8 12) (.block saveMain)))
def valid : Prog isa := .seq prepare (.seq validate compute)
def body : Prog isa := .seq (.block modulusCheck) (.ite .eq valid PublicFn.fail)
def code : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq body (.block PcFn.restore))) (.pop .r12 56)

end VG.Impl.Bignum.Arm.CrtFn
