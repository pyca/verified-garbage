module

public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Recover
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.PointMul
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.Scalar
public import VerifiedGarbage.Impl.Ed25519.PPC64LE.VerifyWindow

/-!
# `vg_ed25519_verify_equation(pk = r3, signature = r4, challenge = r5, scratch = r6)` on PPC64LE

`S < L`, then `A` and `R` decoded by one loop of two iterations into the
tables at 7776 and 7904 (their results ANDed in `r18`; the pointers in
`r29`–`r31`), then `[k] A - [S] B` by 4-bit windows (`VerifyWindow.lean`),
compared projectively with `-R`. The result, 1 or 0, is in `r17`, and
returned in `r3`. `lr` is saved at `LRS` before the static's address
(`adrSym`) changes it.
-/

@[expose] public section

namespace VG.Impl.Ed25519.PPC64LE
open VG.PPC64LE

/-- `r8` zero exactly when `S < L`. -/
def verifyScalar : List Instr := [.addi .r14 .r30 32] ++ unpackField SR 0 ++ scalarCompare

/-- The bytes of the top half of the challenge (at `r31`), or-ed into `r8`: zero exactly when the
challenge is below `2^256`. -/
def challengeHigh : List Instr :=
  [.li .r8 0] ++ (List.range 32).flatMap fun i => [.lbz .r9 .r31 (32 + i), .logic .or .r8 .r8 .r9]

/-- The windows' count: 64 when the challenge is below `2^256` (always, from
`vg_ed25519_verify`, which reduces it modulo `L`), 128 otherwise. The challenge is public. -/
def windowCount : Prog isa :=
  .seq (.block challengeHigh) (.ite (.zero .d .r8) (.block [.li .r15 64]) (.block [.li .r15 128]))

/-- `-R` from the table at 7904 into slots 4–7. -/
def negR : Prog isa :=
  .seq (.block (scratchAddr 7904 ++ pointFromTableQ)) (fieldCode [.const 8 0, .sub 4 8 4, .sub 7 8 7])

/-- `[k]A - [S]B` (`strausPrep`, `windowCount`, `windows`) compared with `-R`. -/
def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7776))
    (.seq strausPrep (.seq windowCount (.seq windows (.seq negR pointEqual))))

def verifyEquationPoints : Prog isa := verifyRhs

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
