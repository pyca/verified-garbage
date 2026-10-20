module

public import VerifiedGarbage.Impl.Ed25519.AArch64.PointDecode
public import VerifiedGarbage.Impl.Ed25519.AArch64.VerifyWindow
public import VerifiedGarbage.Impl.Ed25519.AArch64.Scalar
public import VerifiedGarbage.Spec.Weierstrass

/-! Canonical point/scalar checks and the uncofactored verification equation
with the caller's full 512-bit SHA-512 challenge. -/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64
open VG.AArch64

def loadScalarWords : List Instr :=
  [.ldr .x .x4 .x2 0, .ldr .x .x5 .x2 8, .ldr .x .x6 .x2 16, .ldr .x .x7 .x2 24]

/-- x8 is all ones precisely when the signature scalar is below L. -/
def verifyScalar : List Instr :=
  [ld .x2 7944, .addImm .x .x2 .x2 32, .movz .w .x10 0 0] ++
    loadScalarWords ++ scalarSubtract ++ [.sbcs .x .x8 .x10 .x10]

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]

def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (.ite (.zero .x .x8)
    (.seq (.block (fieldEqual 10 11))
      (.ite (.zero .x .x8) (.block [.movz .w .x8 1 0]) recoverInvalid)) recoverInvalid)

/-- Returns 1 in x8 if `[S]B = R + [k]A`, for `A` at byte 7424 and `R` at byte 7552. -/
def verifyEquationPoints : Prog isa :=
  .seq (.block windowSetup) (.seq aTable (.seq bTable (.seq (.block windowInit)
    (.seq (.block nibbles) (.seq skipZero (.seq windowsA (.seq (.loop nibStepAB (.nonzero .x .x19))
      (.seq (.block negR) pointEqual))))))))

def decodedThen (next : Prog isa) : Prog isa := .ite (.nonzero .x .x8) next recoverInvalid

/-- The word of the working space counting `decodeBoth`'s passes down, 1 (`R`) then 0 (`A`). -/
def DCOUNT : Nat := 7680

/-- The count into `x19` and the encoding's pointer, at byte `7936 + 8 x19`, into `x2`. -/
def decodePtr : List Instr :=
  [ld .x19 DCOUNT, .lsl .x .x2 .x19 3, .add .x .x2 .x2 .x0, .ldr .x .x2 .x2 7936]

/-- The decoded point to byte `7424 + 128 x19` (`A`'s entry, then `R`'s), the count down, and
the count before it into `x19`, which ends the loop after `A`. -/
def decodeStore : List Instr :=
  [ld .x19 DCOUNT] ++ tableAddr 7424 ++ pointToTable ++
    [.subImm .x .x9 .x19 1, st .x9 DCOUNT, .movz .w .x8 1 0]

/-- An encoding that is not a point: 0 in `x8`, and in `x19`, which ends the loop. -/
def decodeFail : List Instr := [.movz .w .x8 0 0, .movz .w .x19 0 0]

def decodeBody : Prog isa :=
  .seq (.block decodePtr) (.seq pointDecode
    (.ite (.nonzero .x .x8) (.block decodeStore) (.block decodeFail)))

/-- `R`, then `A`, decoded by one copy of `pointDecode`, into the table at bytes 7552 and 7424;
`x8` is 1 if both are points, else 0. -/
def decodeBoth : Prog isa :=
  .seq (.block [.movz .w .x19 1 0, st .x19 DCOUNT]) (.loop decodeBody (.nonzero .x .x19))

def verifyDecode : Prog isa := .seq decodeBoth (decodedThen verifyEquationPoints)

def verifyHeaders : List Instr :=
  [.str .x .x0 .x2 7936, .str .x .x1 .x2 7944, .str .x .x8 .x2 7952, mov .x0 .x2]

def verifySetup : List Instr := ([mov .x8 .x2, mov .x2 .x3] : List Instr) ++ scalarSave ++ verifyHeaders

/-- `(pk, sig, challenge, scratch) = (x0, x1, x2, x3)`; boolean result in x0. -/
def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq
    (.seq (.block verifyScalar) (.ite (.nonzero .x .x8) verifyDecode recoverInvalid))
    (.block (([mov .x2 .x0, mov .x0 .x8] : List Instr) ++ scalarRestore)))

end VG.Impl.Ed25519.AArch64
