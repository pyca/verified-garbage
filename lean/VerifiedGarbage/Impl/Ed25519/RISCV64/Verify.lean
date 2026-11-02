module

public import VerifiedGarbage.Impl.Ed25519.RISCV64.Recover
public import VerifiedGarbage.Impl.Ed25519.RISCV64.PointMul
public import VerifiedGarbage.Impl.Ed25519.RISCV64.VerifyWindow

/-!
# `vg_ed25519_verify_equation(pk = a0, signature = a1, challenge = a2, scratch = a3)` on RISC-V

The PPC64LE code (`Impl/Ed25519/PPC64LE/Verify.lean`, ARMv7's): `S < L`,
then `A` and `R` decoded by one loop of two iterations into the tables at
7776 and 7904 (their results ANDed in `s4`; the pointers in `s9`–`s11`),
then `[S] B` (to 8032), `[k] A` (`challengeMul`), the sum with `R` and the projective
comparison. The result, 1 or 0, is in `s3`, and returned in `a0`. The
callee-saved registers and `ra` are saved in the working space at `SAVE`,
which is aligned to 8 bytes. The tables lie beyond the immediates of loads
and stores: their addresses, and the loop's bound, are built with `li32`.
-/

@[expose] public section

namespace VG.Impl.Ed25519.RISCV64
open VG.RISCV64 VG.Impl.Words.RISCV64

/-- Where the callee-saved registers and `ra` are saved. -/
def SAVE : Nat := 1024

/-- The registers saved, in order. -/
def savedRegs : List Reg := [.s0, .s1, .s2, .s3, .s4, .s5, .s6, .s7, .s8, .s9, .s10, .s11, .ra]

def regsSave : List Instr := (List.range 13).map fun i => .store .d (savedRegs.getD i .s0) .a3 (SAVE + 8 * i)

def regsRestore : List Instr := (List.range 13).map fun i => .load .d (savedRegs.getD i .s0) .a3 (SAVE + 8 * i)

/-- `s0 :=` byte `o` of the working space. -/
def scratchAddr (o : Nat) : List Instr := li32 .s0 (BitVec.ofNat 32 o) ++ [.add .s0 .a3 .s0]

def pointTableWrite (o : Nat) : List Instr := scratchAddr o ++ pointToTable

def pointTableRead (o : Nat) : List Instr := scratchAddr o ++ pointFromTable

/-- `a5` zero exactly when the scalar at `SR` is below `L`. -/
def scalarCompare : List Instr := [.li .a5 1] ++ VG.Impl.X25519.RISCV64.pass .a3 SD scalarSubtractSrc

def verifyScalar : List Instr := [.addi .s0 .s10 32] ++ unpackField .s0 SR 0 ++ scalarCompare

/-- The identity at 8032, which `pointEqual` compares `[k]A - [S]B + R` with. -/
def verifyLhs : Prog isa := .seq (constPoint Spec.Ed25519.identity) (.block (pointTableWrite 8032))

def verifyCombine : Prog isa :=
  .seq copyPointToQ (.seq (.block (pointTableRead 7904))
    (.seq addCall (.seq copyPointToQ (.block (pointTableRead 8032)))))

/-- The bytes of the top half of the challenge (at `s11`), or-ed into `a4`: zero
exactly when the challenge is below `2^256`. -/
def challengeHigh : List Instr :=
  [.li .a4 0] ++ (List.range 32).flatMap fun i => [.load .b .a5 .s11 (32 + i), .logic .or .a4 .a4 .a5]

/-- The windows' count: 64 when the challenge is below `2^256` (always, from
`vg_ed25519_verify`, which reduces it modulo `L`), 128 otherwise. The challenge is public. -/
def windowCount : Prog isa :=
  .seq (.block challengeHigh) (.ite (.zero .a4) (.block [.li .s1 64]) (.block [.li .s1 128]))

/-- `[k]A - [S]B` (`strausPrep`, `windowCount`, `windows`), plus `R`, compared with the identity. -/
def verifyRhs : Prog isa :=
  .seq (.block (pointTableRead 7776))
    (.seq strausPrep (.seq windowCount (.seq windows (.seq verifyCombine pointEqual))))

def verifyEquationPoints : Prog isa := .seq verifyLhs verifyRhs

/-! ## Decoding `A` and `R` -/

/-- `A` (`pk`, in `s9`) first, into the table at 7776, then `R` (`s10`) at
7904: the encoding's pointer in `s7`, the table entry's offset in `s8`. -/
def decodeStart : List Instr := [.addi .s7 .s9 0] ++ li32 .s8 (BitVec.ofNat 32 7776) ++ [.li .s4 1]

/-- The decoding's result ANDed into `s4`, the point to the table entry,
then `R`'s pointer and the next entry; `a4` zero after `R`'s. -/
def decodeNext : List Instr :=
  [.logic .and .s4 .s4 .s3, .add .s0 .a3 .s8] ++ pointToTable ++
  [.addi .s7 .s10 0, .addi .s8 .s8 128] ++ li32 .a4 (BitVec.ofNat 32 8032) ++ [.sub .a4 .s8 .a4]

/-- One decoding, of the encoding at `s7`. -/
def decodeBody : Prog isa := .seq (.block [.addi .s0 .s7 0]) (.seq pointDecode (.block decodeNext))

/-- `A` and `R` decoded, by one loop of two iterations. -/
def decodeBoth : Prog isa := .seq (.block decodeStart) (.loop decodeBody (.nonzero .a4))

/-- Both decoded, and the equation if both are points. -/
def verifyDecode : Prog isa :=
  .seq decodeBoth (.ite (.nonzero .s4) verifyEquationPoints recoverInvalid)

def verifyBody : Prog isa :=
  .seq (.block verifyScalar) (.ite (.zero .a5) (.seq (.block initFields) verifyDecode) recoverInvalid)

def verifySetup : List Instr := regsSave ++ [.addi .s9 .a0 0, .addi .s10 .a1 0, .addi .s11 .a2 0]

def verifyFinish : List Instr := [.addi .a0 .s3 0] ++ regsRestore

def verifyEquation : Prog isa :=
  .seq (.block verifySetup) (.seq verifyBody (.block verifyFinish))

end VG.Impl.Ed25519.RISCV64
