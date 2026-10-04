import VerifiedGarbage.Impl.Ed25519.X86.InputSlice
import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
import VerifiedGarbage.Impl.Ed25519.X86.ScalarBase
import VerifiedGarbage.Impl.Ed25519.X86.Scalar
import VerifiedGarbage.Impl.Ed25519.X86.VerifyWindow

/-! Canonical decoding and the uncofactored verification equation using all
512 supplied challenge bits. The four cdecl arguments are pk, sig, challenge,
and scratch; the result is exactly zero or one in EAX. -/
namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def verifyScalar : List Instr := inputSliceWords 1 32 64 8 ++ scalarSubtract ++ [.alu .test .ebx (.reg .ebx)]

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]
def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ fieldEqual 8 9)) (.ite .e
    (.seq (.block (fieldEqual 10 11)) (.ite .e (.block [.mov .eax (.imm 1)]) recoverInvalid)) recoverInvalid)

/-- Returns 1 in `eax` if `[S]B = R + [k]A`, for `A` at byte 7680 and `R` at byte 7808: the
windows' `[k]A - [S]B` compared with `-R`. -/
def verifyEquationPoints : Prog isa := .seq windowMultiply (.seq (.block negR) pointEqual)

def decodedThen (next : Prog isa) : Prog isa :=
  .seq (.block [.alu .test .eax (.reg .eax)]) (.ite .ne next recoverInvalid)

def verifyDecodeR : Prog isa :=
  .seq (.block (inputSliceWords 1 0 96 8)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7808)) verifyEquationPoints)))

def verifyDecodeA : Prog isa :=
  .seq (.block (inputSliceWords 0 0 96 8)) (.seq pointDecode
    (decodedThen (.seq (.block (pointTableWrite 7680)) verifyDecodeR)))

def verifyFinish : List Instr := [.mov .edx (.reg .eax)] ++ restore ++ [.mov .eax (.reg .edx)]

def verifyEquation : Prog isa :=
  .seq (.block (abiSave 3)) (.seq
    (.seq (.block verifyScalar) (.ite .e verifyDecodeA recoverInvalid)) (.block verifyFinish))

end VG.Impl.Ed25519.X86
