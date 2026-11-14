module

public import VerifiedGarbage.Impl.Bignum.Arm.PublicFn
public import VerifiedGarbage.Impl.Bignum.Arm.CrtSetup
public import VerifiedGarbage.Impl.Bignum.Arm.CrtWorkspaceCall
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
workspace. Its conditional branches test public values only: the modulus
check, and whether a factor's width leaves high limbs of the input to copy.
All secret validation bits accumulate at slot 48 and mask the final output.
Each factor's power, and the coefficient, run in the narrow workspace at a
factor's own width.
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
/-- The checks, `p q = n` by `product`. -/
def validateWith (product : Prog isa) : Prog isa :=
  .seq acceptInput (.seq loadP (.seq loadQ (.seq product (.block mergeAcceptance))))
def validate : Prog isa := validateWith validateProduct

/-! The pipeline, with the factors prepared by `prime` and the key checked by
`check`: `narrowPrime` and `validate` for `vg_rsa_private_crt`. -/

def powerOf (prime : Nat → Prog isa) (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  .seq (selectChild slot) (.seq (narrowPowerOf prime phase slot primeSlot exponentSlot) selectMain)
def qSource : List Instr := [.ldrSp .r1 8, .ldr .r1 .r1 228]
/-- `m_q` and `qInv` into arrays 1 and 4 of p's full workspace, and array 5 cleared for `h`. -/
def coefficientInput : Prog isa :=
  .seq (.block qSource) (.seq (transferArray 1 6) (.seq (savedOperand 4 96 100) (clearOperandBuffer 104)))
def coefficientPhaseOf (prime : Nat → Prog isa) : Prog isa := .seq (selectChild 224)
  (.seq coefficientInput (.seq (enterNarrow 68) (.seq (prime 64) (.seq coefficient selectMain))))
def outputArgs : List Instr := [.ldr .r1 .r0 232, .ldrSp .r4 4, .ldrSp .r6 12]
def finish : Prog isa := .seq (.block qSource) (.seq (transferArray 1 6)
  (.seq recombine (.seq (.block outputArgs) exportBufferMasked)))
def computeOf (prime : Nat → Prog isa) (phase : Prog isa) : Prog isa := .seq (powerOf prime phase 224 64 80)
  (.seq (powerOf prime phase 228 72 88) (.seq (coefficientPhaseOf prime) finish))

def prepare : Prog isa := .seq (.block PcFn.head) (.seq setupAll
  (.seq (savedOperand 0 8 12) (.block saveMain)))
def validOf (check : Prog isa) (prime : Nat → Prog isa) (phase : Prog isa) : Prog isa :=
  .seq prepare (.seq check (computeOf prime phase))
def bodyOf (check : Prog isa) (prime : Nat → Prog isa) (phase : Prog isa) : Prog isa :=
  .seq (.block modulusCheck) (.ite .eq (validOf check prime phase) PublicFn.fail)
def codeOf (check : Prog isa) (prime : Nat → Prog isa) (phase : Prog isa) : Prog isa :=
  .frame (.push [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r8, .r9, .r10, .r11, .r12, .lr])
    (.seq (.block entry) (.seq (bodyOf check prime phase) (.block PcFn.restore))) (.pop .r12 56)

def powerWith (phase : Prog isa) (slot primeSlot exponentSlot : Nat) : Prog isa :=
  powerOf narrowPrime phase slot primeSlot exponentSlot
def coefficientPhase : Prog isa := coefficientPhaseOf narrowPrime
def computeWith (phase : Prog isa) : Prog isa := computeOf narrowPrime phase
def validWith (phase : Prog isa) : Prog isa := validOf validate narrowPrime phase
def bodyWith (phase : Prog isa) : Prog isa := bodyOf validate narrowPrime phase
def codeWith (phase : Prog isa) : Prog isa := codeOf validate narrowPrime phase

def code : Prog isa := codeWith windowExpPhase

end VG.Impl.Bignum.Arm.CrtFn
