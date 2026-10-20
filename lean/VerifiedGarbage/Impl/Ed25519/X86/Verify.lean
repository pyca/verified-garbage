module

public import VerifiedGarbage.Impl.Ed25519.X86.InputSlice
public import VerifiedGarbage.Impl.Ed25519.X86.PointDecode
public import VerifiedGarbage.Impl.Ed25519.X86.Scalar
public import VerifiedGarbage.Impl.Ed25519.X86.VerifyWindow

/-! Canonical decoding and the uncofactored verification equation using all
512 supplied challenge bits. The four cdecl arguments are pk, sig, challenge,
and scratch; the result is exactly zero or one in EAX. -/

@[expose] public section

namespace VG.Impl.Ed25519.X86
open VG VG.X86 VG.Impl.X25519.X86

def verifyScalar : List Instr := inputSliceWords 1 32 64 8 ++ scalarSubtract ++ [.alu .test .ebx (.reg .ebx)]

def pointEqualOps : List FieldOp := [.mul 8 0 6, .mul 9 4 2, .mul 10 1 6, .mul 11 5 2]
/-- Slots 8 and 9 compared: if equal, slots 10 and 11 copied into them, `eax = 1` and `esi`
counted down; otherwise `eax = 0` and `esi = 0`. ZF is clear while another comparison follows. -/
def equalStep : Prog isa :=
  .seq (.block (fieldEqual 8 9)) (.ite .e
    (.block (fieldCode [.copy 8 10, .copy 9 11] ++ [.mov .eax (.imm 1), .alu .sub .esi (.imm 1)]))
    (.block [.mov .eax (.imm 0), .mov .esi (.imm 0), .alu .test .esi (.reg .esi)]))

/-- `eax = 1` if the points in slots 0–3 and 4–7 are equal (`X₁Z₂ = X₂Z₁` and `Y₁Z₂ = Y₂Z₁`):
the two comparisons, by two passes of `equalStep`. -/
def pointEqual : Prog isa :=
  .seq (.block (fieldCode pointEqualOps ++ [.mov .esi (.imm 2)])) (.loop equalStep .ne)

/-- Returns 1 in `eax` if `[S]B = R + [k]A`, for `A` at byte 7680 and `R` at byte 7808: the
windows' `[k]A - [S]B` compared with `-R`. -/
def verifyEquationPoints : Prog isa := .seq bTable (.seq windowMultiply (.seq (.block negR) pointEqual))

/-! ## Decoding `A` and `R` -/

/-- The working space's words of the decodings' loop, past `R`'s table entry: the encoding's
pointer, `R`'s, the table entry's offset, and the AND of the decodings' results. -/
def DPTR : Nat := 7936
def DNEXT : Nat := 7940
def DTAB : Nat := 7944
def DOK : Nat := 7948

/-- `A` (`pk`) first, then `R` (the signature's first half), into the table at 7680, then 7808. -/
def decodeStart : List Instr :=
  [.mov .eax (.mem (at_ .esp 4)), .store (sc DPTR) .eax, .mov .eax (.mem (at_ .esp 8)),
    .store (sc DNEXT) .eax, .mov .eax (.imm 7680), .store (sc DTAB) .eax, .mov .eax (.imm 1),
    .store (sc DOK) .eax]

/-- The encoding at `[DPTR]` copied to slot 3. -/
def decodeLoad : List Instr := .mov .esi (.mem (sc DPTR)) :: copyWords 96 8

/-- The point to the table at `[DTAB]` (with the decoding's result kept in `ecx`), the result
ANDed into `DOK`, then `R`'s pointer and the next entry; `ZF` set after `R`'s. -/
def decodeNext : List Instr :=
  [.mov .ecx (.reg .eax), .mov .edx (.mem (sc DTAB)), .alu .add .edx (.reg .edi)] ++ pointToTable ++
  [.mov .edx (.mem (sc DOK)), .alu .and .edx (.reg .ecx), .store (sc DOK) .edx,
    .mov .eax (.mem (sc DNEXT)), .store (sc DPTR) .eax, .mov .edx (.mem (sc DTAB)),
    .alu .add .edx (.imm 128), .store (sc DTAB) .edx, .alu .cmp .edx (.imm 7936)]

/-- One decoding. -/
def decodeBody : Prog isa := .seq (.block decodeLoad) (.seq pointDecode (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth : Prog isa := .seq (.block decodeStart) (.loop decodeBody .ne)

/-- Both decoded, and the equation if both are points. -/
def verifyDecode : Prog isa :=
  .seq decodeBoth (.seq (.block [.mov .eax (.mem (sc DOK)), .alu .test .eax (.reg .eax)])
    (.ite .ne verifyEquationPoints recoverInvalid))

def verifyFinish : List Instr := [.mov .edx (.reg .eax)] ++ restore ++ [.mov .eax (.reg .edx)]

def verifyEquation : Prog isa :=
  .seq (.block (abiSave 3)) (.seq
    (.seq (.block verifyScalar) (.ite .e verifyDecode recoverInvalid)) (.block verifyFinish))

end VG.Impl.Ed25519.X86
