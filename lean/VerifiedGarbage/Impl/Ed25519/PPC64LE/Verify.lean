module

import VerifiedGarbage.Impl.Ed25519.PPC64LE.ScalarBase
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Recover
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar

/-!
# `vg_ed25519_verify_equation(pk = r3, signature = r4, challenge = r5, scratch = r6)` on PPC64LE

ARMv7's (`Impl/Ed25519/Arm/Verify.lean`): `S < L`, then `A` and `R`
decoded by one loop of two iterations into the tables at 7776 and 7904
(their results ANDed in `r18`; the pointers in `r29`–`r31`), then `[S] B` (to 8032), `[k] A`, the sum
with `R` and the projective comparison. The result, 1 or 0, is in `r17`,
and returned in `r3`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

/-- `r8` zero exactly when `S < L`. -/
def verifyScalar : List Instr := [.addi .r14 .r30 32] ++ unpackField SR 0 ++ scalarCompare

def verifyLhs : Prog isa :=
  .seq (.block [.addi .r14 .r30 32])
    (.seq (constPoint Spec.Ed25519.basePoint)
      (.seq (pointFromScalar 16) (.block (pointTableWrite 8032))))

def verifyCombine : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7904))
    (.seq addCall (.seq copyPointToQ (.block (pointTableRead 8032)))))

def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7776 ++ [.addi .r14 .r31 0]))
    (.seq (pointFromScalar 32) (.seq verifyCombine pointEqual))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs

/-! ## Decoding `A` and `R` -/

/-- `A` (`pk`, in `r29`) first, into the table at 7776, then `R` (`r30`) at
7904: the encoding's pointer in `r27`, the table entry's offset in `r28`. -/
def decodeStart : List Instr := [.addi .r27 .r29 0, .li .r28 7776, .li .r18 1]

/-- The decoding's result ANDed into `r18`, the point to the table entry,
then `R`'s pointer and the next entry; `r7` zero after `R`'s. -/
def decodeNext : List Instr :=
  [.logic .and .r18 .r18 .r17, .add .r14 .r6 .r28] ++ pointToTable ++
  [.addi .r27 .r30 0, .addi .r28 .r28 128, .subi .r7 .r28 8032]

/-- One decoding, of the encoding at `r27`. -/
def decodeBody : Prog isa := .seq (.block [.addi .r14 .r27 0]) (.seq pointDecode (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth : Prog isa := .seq (.block decodeStart) (.loop decodeBody (.nonzero .d .r7))

/-- Both decoded, and the equation if both are points. -/
def verifyDecode : Prog isa :=
  .seq decodeBoth (.ite (.nonzero .d .r18) verifyEquationPoints recoverInvalid)

def verifyBody : Prog isa :=
  .seq (.block verifyScalar) (.ite (.zero .d .r8) (.seq (.block initFields) verifyDecode) recoverInvalid)

def verifySetup : List Instr :=
  scalarSave .r6 ++ [.addi .r29 .r3 0, .addi .r30 .r4 0, .addi .r31 .r5 0, .mflr .r7,
    .store .d .r7 .r6 LRS]

def verifyFinish : List Instr :=
  [.load .d .r7 .r6 LRS, .mtlr .r7, .addi .r3 .r17 0] ++ scalarRestore

def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq verifyBody (.block verifyFinish))

end VG.Impl.Ed25519.PPC64LE
