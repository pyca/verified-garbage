module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks
public import VerifiedGarbage.Impl.Dsa.AArch64.Workspace

/-! # Complete DSA programs using the AAPCS64 argument layout

Only caller-saved registers are used. Child arithmetic preserves all other
registers, including the link register, and the stack pointer.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.SignVerify
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout

def initial (src : Reg) (f : Field) : Instr := .str .x src .x11 f.offset

def keyPointers : List Instr :=
  [.ldr .x .x3 .x11 Field.p.offset, .ldr .x .x12 .x11 Field.pLen.offset,
    .add .x .x3 .x3 .x12, initial .x3 .q,
    .ldr .x .x13 .x11 Field.qLen.offset, .add .x .x3 .x3 .x13, initial .x3 .g,
    .add .x .x3 .x3 .x12, initial .x3 .y,
    .add .x .x3 .x3 .x12, initial .x3 .x, mov .x0 .x11]

def signFields : List Instr :=
  [movi .x12 0, initial .x12 .signature, initial .x0 .out, initial .x2 .p,
    initial .x4 .pLen, initial .x5 .nonce, initial .x6 .qLen, initial .x7 .digest,
    .ldrSp .x12 0, initial .x12 .digestLen]

def verifyFields : List Instr :=
  [movi .x12 0, initial .x12 .out, initial .x12 .nonce, initial .x0 .p,
    initial .x2 .pLen, initial .x3 .qLen, initial .x4 .signature,
    initial .x6 .digest, initial .x7 .digestLen]

def signEntry : List Instr :=
  ([.ldrSp .x11 8] : List Instr) ++ signFields ++ keyPointers

def verifyEntry : List Instr :=
  ([.ldrSp .x11 0] : List Instr) ++ verifyFields ++ keyPointers

def copyMaskedByte : List Instr :=
  [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x8, .strb .x3 .x2 0,
    .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]

def writeScalar (offset : Nat) (second : Bool) : Prog isa := seqs [
  .block (([movi .x3 offset, .add .x .x1 .x0 .x3,
    Core.field .x2 .out, Core.field .x9 .qLen, Core.field .x8 .mask] : List Instr) ++
    (if second then [.add .x .x2 .x2 .x9] else [])),
  .loop (.block copyMaskedByte) (.nonzero .x .x9)]

def result : List Instr :=
  [Core.field .x3 .mask, movi .x0 1, .logic .and .x .x0 .x3 .x0]

def signFailure : Prog isa := seqs [
  .block [Core.field .x1 .out, Core.field .x2 .qLen, .add .x .x2 .x2 .x2, movi .x3 0],
  countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1],
  .block [movi .x0 0]]

def sign (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block signEntry, Checks.domainShape,
  .ite (.zero .x .x3) signFailure (seqs [workspaces, Checks.signingKey mul,
    Checks.privateKey mul, Core.sign mul, Checks.zero (Core.scalar r) true,
    Checks.zero (Core.scalar s) true, writeScalar r false, writeScalar s true, .block result])]

def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block verifyEntry, Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0]) (seqs [workspaces, Checks.publicKey mul,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify mul, Checks.equal (Core.scalar u) Core.signatureR, .block result])]

end VG.Impl.Dsa.AArch64.SignVerify
