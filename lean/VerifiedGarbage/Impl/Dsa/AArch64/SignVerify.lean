module

public import VerifiedGarbage.Impl.Dsa.AArch64.Checks

/-!
# Complete DSA sign/verify programs on AArch64

AAPCS64 arguments follow `Spec/Dsa/SignVerify.lean`: the first eight in
`x0`–`x7`, the others on the stack. `vg_dsa_sign(out, out_len, key,
key_len, p_len, nonce, q_len, digest, digest_len, scratch, scratch_len)`
has `digest_len`, `scratch` and `scratch_len` at `[sp]`, `[sp, #8]` and
`[sp, #16]`; `vg_dsa_verify(key, key_len, p_len, q_len, signature,
signature_len, digest, digest_len, scratch, scratch_len)` has `scratch` and
`scratch_len` at `[sp]` and `[sp, #8]`.

Caller-provided scratch contains the saved arguments, two Montgomery
workspaces and computed operands, as on x86-64
(`Impl/Dsa/X86_64/SignVerify.lean`, `Impl/Dsa/Layout.lean`). The code
writes no callee-saved register, and uses no stack: the Montgomery
multiplication's calls keep the return address in `v31`.
-/

@[expose] public section

namespace VG.Impl.Dsa.AArch64.SignVerify

open VG VG.AArch64 VG.Impl.Bignum VG.Impl.Bignum.AArch64 VG.Impl.Bignum.Public
open VG.Impl.Rsa.AArch64 VG.Impl.Dsa.Layout

/-- Store `t` in a field relative to the scratch pointer in `x8` during entry. -/
def initial (t : Reg) (f : Field) : Instr := .str .x t .x8 f.offset

/-- A field relative to `x8` into `t`. -/
def initialLoad (t : Reg) (f : Field) : Instr := .ldr .x t .x8 f.offset

/-- Unpack key component pointers once the common fields are saved, then
make the scratch pointer the outer workspace's base. -/
def keyPointers : List Instr :=
  [initialLoad .x3 .p, initialLoad .x4 .pLen, initialLoad .x5 .qLen,
    .add .x .x3 .x3 .x4, initial .x3 .q, .add .x .x3 .x3 .x5, initial .x3 .g,
    .add .x .x3 .x3 .x4, initial .x3 .y, .add .x .x3 .x3 .x4, initial .x3 .x,
    mov .x0 .x8]

/-- Signing: `digest_len` and `scratch` are the first two stack arguments. -/
def signEntry : List Instr :=
  [.ldrSp .x8 8, movi .x3 0, initial .x3 .signature,
    initial .x0 .out, initial .x2 .p, initial .x4 .pLen, initial .x5 .nonce,
    initial .x6 .qLen, initial .x7 .digest, .ldrSp .x3 0, initial .x3 .digestLen] ++ keyPointers

/-- Verification: `scratch` is the first stack argument. -/
def verifyEntry : List Instr :=
  [.ldrSp .x8 0, movi .x9 0, initial .x9 .out, initial .x9 .nonce,
    initial .x0 .p, initial .x2 .pLen, initial .x3 .qLen, initial .x4 .signature,
    initial .x6 .digest, initial .x7 .digestLen] ++ keyPointers

/-- The parent workspace's structural header. Its arrays are not used by
Montgomery arithmetic; array zero holds the saved DSA arguments. -/
def parent : List Instr :=
  ([movi .x12 outerWords, sth .x12 sW, movi .x3 0, sth .x3 sMinv] : List Instr) ++ setBases

/-- Initialize a child workspace and its odd modulus. This runs only after
the public shape checks; its width is ceil(component_len / 8), at least 3. -/
def child (offset : Nat) (modulus : Operand) : Prog isa := seqs [
  .block (Core.operand arg argLen modulus ++
    ([mov .x1 .x0, ldh .x12 argLen, .addImm .x .x12 .x12 7, .lsr .x .x12 .x12 3] : List Instr) ++
    Core.enter offset ++ ([sth .x12 sW, sth .x1 Crt.sLink] : List Instr) ++ setBases),
  Arithmetic.load aN arg argLen,
  .block (([ldh .x3 (sArr aN), ld .x3 .x3] : List Instr) ++ minv ++ ([sth .x15 sMinv, Crt.leave] : List Instr))]

def workspaces : Prog isa := seqs [
  .block parent,
  child pWorkspace ⟨.input .p, .pLen⟩,
  child qWorkspace ⟨.input .q, .qLen⟩]

/-- Copy one computed scalar under the final success mask. When second is
true the destination begins q_len bytes after out. -/
def writeScalar (offset : Nat) (second : Bool) : Prog isa := seqs [
  .block (([.movz .x .x1 (BitVec.ofNat 16 offset) 0, .add .x .x1 .x0 .x1,
    Core.field .x2 .out, Core.field .x9 .qLen, Core.field .x8 .mask] : List Instr) ++
    (if second then [.add .x .x2 .x2 .x9] else [])),
  .loop (.block [.ldrb .x3 .x1 0, .logic .and .x .x3 .x3 .x8, .strb .x3 .x2 0,
    .addImm .x .x1 .x1 1, .addImm .x .x2 .x2 1, .subImm .x .x9 .x9 1]) (.nonzero .x .x9)]

/-- Return the success bit. -/
def result : List Instr := [Core.field .x3 .mask, movi .x4 1, .logic .and .x .x0 .x3 .x4]

/-- Early failure on a public, malformed domain must zero the entire
signature without reading uninitialized scalar scratch. -/
def signFailure : Prog isa := seqs [
  .block [Core.field .x1 .out, Core.field .x9 .qLen, .add .x .x9 .x9 .x9, movi .x3 0],
  .loop (.block [.strb .x3 .x1 0, .addImm .x .x1 .x1 1, .subImm .x .x9 .x9 1]) (.nonzero .x .x9),
  .block [movi .x0 0]]

def sign (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block signEntry,
  Checks.domainShape,
  .ite (.zero .x .x3) signFailure (seqs [
    workspaces, Checks.publicKey mul, Checks.privateKey mul,
    Core.sign mul, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
    writeScalar r false, writeScalar s true, .block result])]

def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block verifyEntry,
  Checks.domainShape,
  .ite (.zero .x .x3) (.block [movi .x0 0]) (seqs [
    workspaces, Checks.publicKey mul,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify mul, Checks.equal (Core.scalar u) Core.signatureR,
    .block result])]

end VG.Impl.Dsa.AArch64.SignVerify
