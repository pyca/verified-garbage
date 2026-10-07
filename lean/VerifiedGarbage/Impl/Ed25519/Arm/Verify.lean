import VerifiedGarbage.Impl.Ed25519.Arm.PointDecode
import VerifiedGarbage.Impl.Ed25519.Arm.PointEqual
import VerifiedGarbage.Impl.Ed25519.Arm.PointTableIO
import VerifiedGarbage.Impl.Ed25519.Arm.PointFromScalar
import VerifiedGarbage.Impl.Ed25519.Arm.ScalarABI

/-! Strict Ed25519 verification with the entire 512-bit challenge. -/
namespace VG.Impl.Ed25519.Arm
open VG.Arm

def loadHeader (d : Nat) : List Instr := scratchAddr d ++ [.ldr .r12 .r12 0]
def verifyScalar : List Instr :=
  loadHeader 8132 ++ [.dp .add .r12 .r12 (.imm 32)] ++
    unpackField SR 0 ++ scalarCompare ++ [.cmp .r5 (.imm 0)]

def verifyLhs : Prog isa :=
  .seq (.block (loadHeader 8132 ++ [.dp .add .r12 .r12 (.imm 32)]))
    (.seq (constPoint Spec.Ed25519.basePoint)
      (.seq (pointFromScalar 16) (.block (pointTableWrite 8000))))

def verifyCombine : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7872))
    (.seq pointAdd (.seq copyPointToQ (.block (pointTableRead 8000)))))

def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7744 ++ loadHeader 8136))
    (.seq (pointFromScalar 32) (.seq verifyCombine pointEqual))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs
/-! ## Decoding `A` and `R` -/

/-- The working space's words of the decodings' loop: the encoding's pointer, the table
entry's offset, and the AND of the decodings' results. -/
def DPTR : Nat := 32
def DTAB : Nat := 36
def DOK : Nat := 40

/-- `A` (`pk`, from its header at 8128) first, into the table at 7744, then `R` at 7872. -/
def decodeStart : List Instr :=
  loadHeader 8128 ++ [.str .r12 .r0 DPTR, .movw .r3 7744, .str .r3 .r0 DTAB, .mov .r3 (.imm 1),
    .str .r3 .r0 DOK]

/-- The decoding's result ANDed into `DOK`, the point to the table at `[DTAB]`, then `R`'s
pointer (its header at 8132) and the next entry; `Z` set after `R`'s. -/
def decodeNext : List Instr :=
  [.ldr .r3 .r0 DOK, .dp .and .r3 .r3 (.reg .r9), .str .r3 .r0 DOK, .ldr .r12 .r0 DTAB,
    .dp .add .r12 .r0 (.reg .r12)] ++ pointToTable ++ loadHeader 8132 ++
  [.str .r12 .r0 DPTR, .ldr .r3 .r0 DTAB, .dp .add .r3 .r3 (.imm 128), .str .r3 .r0 DTAB,
    .cmp .r3 (.imm 8000)]

/-- One decoding, of the encoding at `[DPTR]`. -/
def decodeBody : Prog isa := .seq (.block [.ldr .r12 .r0 DPTR]) (.seq pointDecode (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth : Prog isa := .seq (.block decodeStart) (.loop decodeBody .ne)

/-- Both decoded, and the equation if both are points. -/
def verifyDecode : Prog isa :=
  .seq decodeBoth (.seq (.block [.ldr .r9 .r0 DOK, .cmp .r9 (.imm 0)])
    (.ite .ne verifyEquationPoints recoverInvalid))

def verifyBody : Prog isa :=
  .seq (.block verifyScalar) (.ite .eq (.seq (.block initFields) verifyDecode) recoverInvalid)

def verifyHeaders : List Instr :=
  [.movw .r12 8128, .dp .add .r12 .r3 (.reg .r12),
    .str .r0 .r12 0, .str .r1 .r12 4, .str .r2 .r12 8, .mov .r0 (.reg .r3)]
def verifySetup : List Instr := scalarSave .r3 ++ verifyHeaders
def verifyFinish : List Instr :=
  [.mov .r1 (.reg .r9)] ++ scalarRestore ++ [.mov .r0 (.reg .r1)]
def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq verifyBody (.block verifyFinish))

end VG.Impl.Ed25519.Arm
