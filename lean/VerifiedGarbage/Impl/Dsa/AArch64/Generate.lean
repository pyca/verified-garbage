module

public import VerifiedGarbage.Impl.Dsa.AArch64.SignVerify

/-! # AAPCS64 DSA domain checking and private-key derivation

The domain check uses g as the public value in the signer's algebraic
checks. Derivation computes y = g^x, checks the resulting key, and masks
every output byte on failure. All registers used are caller-saved.
-/

@[expose] public section
namespace VG.Impl.Dsa.AArch64.Generate
open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Dsa.Layout SignVerify

def checkFields : List Instr :=
  [movi .x12 0, initial .x12 .signature, initial .x12 .out,
    initial .x12 .nonce, initial .x12 .digest, initial .x12 .digestLen,
    initial .x0 .p, initial .x2 .pLen, initial .x3 .qLen]

def checkEntry : List Instr :=
  ([mov .x11 .x4] : List Instr) ++ checkFields ++ keyPointers ++
  [.ldr .x .x3 .x11 Field.g.offset, initial .x3 .y]

def deriveFields : List Instr :=
  [movi .x12 0, initial .x12 .signature, initial .x12 .nonce,
    initial .x12 .digest, initial .x12 .digestLen,
    initial .x0 .out, initial .x2 .p, initial .x4 .pLen, initial .x6 .qLen]

def deriveEntry : List Instr :=
  ([mov .x11 .x7] : List Instr) ++ deriveFields ++ keyPointers ++
  [initial .x5 .x, movi .x3 derivedY, .add .x .x3 .x11 .x3, initial .x3 .y]

def copyMasked : Prog isa :=
  .loop (.block copyMaskedByte) (.nonzero .x .x9)

def copyY : Prog isa := seqs [
  .block [movi .x3 t2, .add .x .x1 .x0 .x3,
    movi .x3 derivedY, .add .x .x2 .x0 .x3, Core.field .x9 .pLen,
    movi .x8 0, .subImm .x .x8 .x8 1], copyMasked]

def keyHead : List Instr :=
  [Core.field .x8 .mask, Core.field .x10 .out, Core.field .x11 .y,
    Core.field .x12 .x, Core.field .x13 .pLen, Core.field .x14 .qLen,
    mov .x2 .x10, Core.field .x1 .p, .add .x .x9 .x13 .x13, .add .x .x9 .x9 .x14]

def writeKey : Prog isa := seqs [
  .block keyHead, copyMasked,
  .block [.add .x .x2 .x10 .x13, .add .x .x2 .x2 .x13,
    .add .x .x2 .x2 .x14, mov .x1 .x11, mov .x9 .x13], copyMasked,
  .block [.add .x .x2 .x10 .x13, .add .x .x2 .x2 .x13,
    .add .x .x2 .x2 .x13, .add .x .x2 .x2 .x14,
    mov .x1 .x12, mov .x9 .x14], copyMasked]

def deriveFailure : Prog isa := seqs [
  .block [Core.field .x1 .out, Core.field .x2 .pLen,
    .add .x .x3 .x2 .x2, .add .x .x2 .x3 .x2,
    Core.field .x3 .qLen, .add .x .x2 .x2 .x3,
    .add .x .x2 .x2 .x3, movi .x3 0],
  countLoop .x2 [.strb .x3 .x1 0, .addImm .x .x1 .x1 1],
  .block [movi .x0 0]]

def checkParameters (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block checkEntry, Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0])
    (seqs [workspaces, Checks.signingKey mul, .block result])]

def deriveKey (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block deriveEntry, Checks.domainShape,
  .ite (.zero .x .x3) deriveFailure (seqs [
    workspaces, Checks.range qWorkspace Core.privateScalar,
    Core.pow mul pWorkspace Core.generator Core.privateScalar (Core.element t2),
    copyY, Checks.signingKey mul, writeKey, .block result])]

end VG.Impl.Dsa.AArch64.Generate
