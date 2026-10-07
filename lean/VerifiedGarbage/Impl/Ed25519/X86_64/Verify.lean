import VerifiedGarbage.Impl.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86_64.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86_64.VerifyWindow

/-! Strict verification with the full 512-bit challenge supplied by the caller. -/

namespace VG.Impl.Ed25519.X86_64

open VG.X86_64
open VG.Impl.X25519.X86_64 (at_ sc loadU loads store4)

/-- Tail storage survives scalar multiplication's checkpoint and local tables. -/
def pointTableWrite (o : Nat) : List Instr :=
  [.movImm64 .rbx 0] ++ tableAddr o ++ pointToTable

def loadScalarWords : List Instr :=
  [.mov .r8 (.mem (at_ .rdx 0)), .mov .r9 (.mem (at_ .rdx 8)),
    .mov .r10 (.mem (at_ .rdx 16)), .mov .r11 (.mem (at_ .rdx 24))]

def verifyScalar : List Instr :=
  [.mov .rdx (.mem (sc 7944)), .alu .add .rdx (.imm 32)] ++ loadScalarWords ++ scalarSubtract

/-- Compare [X:Y:Z] in slots 0-3 and 4-7 without inversion. -/
def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]

def pointEqual (fld : Arith) : Prog isa :=
  .seq (.block (fieldCode fld pointEqualOps ++ fieldEqual fld 8 9)) (.ite .e
    (.seq (.block (fieldEqual fld 10 11)) (.ite .e (.block [.mov32 .rax (.imm 1)]) recoverInvalid))
    recoverInvalid)

/-- Returns 1 in `rax` if `[S]B = R + [k]A`, for `A` at byte 7424 and `R` at byte 7552,
with the windows `win` (`windows`). -/
def verifyEquationPoints (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (.block windowSetup) (.seq (aTable fld) (.seq (.block (windowInit fld))
    (.seq skipZero (.seq recodeAll (.seq win (.seq (.block (negR fld)) (pointEqual fld)))))))

/-- The 32 bytes at `rdx`, their top bit masked, into slot 1, and the power's input of that
y-coordinate into slot `o`. -/
def decodeInput (fld : Arith) (o : Slot) : List Instr :=
  loadU ++ store4 (offset 1) ++ fieldCode fld (rootInputOps o)

/-- Slot 19 to byte 7680 of the scratch, which decoding A keeps. -/
def powerSave : List Instr := [.mov .rax (.reg .rdi)] ++ loads (offset 19) .r8 .r9 .r10 .r11 ++ tableWords 7680

/-- Byte 7680 of the scratch back to slot 15. -/
def powerRestore : List Instr := [.mov .rax (.reg .rdi)] ++ fromTableWords 7680 ++ store4 (offset 15)

/-- The powers of A (at byte 7936's pointer) into slot 15, and of R (at byte 7944's) into byte
7680. -/
def decodePowers (fld : Arith) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (sc 7944))]) <| .seq (.block (decodeInput fld 3)) <|
  .seq (.block [.mov .rdx (.mem (sc 7936))]) <| .seq (.block (decodeInput fld 2)) <|
  .seq (rootPower2 fld) (.block powerSave)

/-- Continue only when a point decoder returned success. -/
def decodedThen (next : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .rax (.reg .rax)]) (.ite .ne next recoverInvalid)

/-- R decoded, with its power in slot 15, then the equation. -/
def decodeRThen (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (sc 7944))]) (.seq (pointDecode fld)
    (decodedThen (.seq (.block (pointTableWrite 7552)) (verifyEquationPoints fld win))))

/-- R's power back into slot 15, then R decoded. -/
def verifyDecodeR (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (.block powerRestore) (decodeRThen fld win)

/-- A decoded, with its power in slot 15, then R. -/
def decodeAThen (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (.block [.mov .rdx (.mem (sc 7936))]) (.seq (pointDecode fld)
    (decodedThen (.seq (.block (pointTableWrite 7424)) (verifyDecodeR fld win))))

/-- Both powers (`decodePowers`), then A decoded. -/
def verifyDecodeA (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (decodePowers fld) (decodeAThen fld win)

/-- The inputs' addresses, and the static's (`baseOddSym`), to bytes 7936–7967 of the scratch. -/
def verifyHeaders : List Instr :=
  [.store (at_ .rdx 7936) .rdi, .store (at_ .rdx 7944) .rsi,
    .store (at_ .rdx 7952) .rax, .mov .rdi (.reg .rdx), .leaSym .rax baseOddSym,
    .store (sc 7960) .rax]

def verifySetup : List Instr :=
  ([.mov .rax (.reg .rdx), .mov .rdx (.reg .rcx)] : List Instr) ++ scalarSave ++ verifyHeaders

/-- Verification, with the field arithmetic `fld` and the windows `win`. -/
def verifyEquation (fld : Arith) (win : Prog isa) : Prog isa :=
  .seq (.block verifySetup) (.seq
    (.seq (.block verifyScalar) (.ite .b (verifyDecodeA fld win) recoverInvalid))
    (.block (([.mov .rdx (.reg .rdi)] : List Instr) ++ scalarRestore)))

end VG.Impl.Ed25519.X86_64
