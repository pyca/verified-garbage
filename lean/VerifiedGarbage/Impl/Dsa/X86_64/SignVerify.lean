import VerifiedGarbage.Impl.Dsa.X86_64.Checks

/-!
# Complete DSA sign/verify programs on x86-64

System V arguments follow Spec/Dsa/SignVerify.lean. Caller-provided scratch
contains the saved callee-saved registers, two Montgomery workspaces and
computed operands. This file defines programs only; emitting them requires
whole-operation correctness, memory-safety, ABI and constant-time proofs.
-/
namespace VG.Impl.Dsa.X86_64.SignVerify

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout

/-- A field stored relative to the scratch pointer in r11 during entry. -/
def initial (f : Field) : MemOp := { base := .r11, disp := f.offset }

/-- Save all callee-saved registers before using the scratch allocation. -/
def save : List Instr :=
  saved.zipIdx.map fun (reg, i) => .store { base := .r11, disp := 8 * i } reg

/-- Unpack key component pointers once the common fields are saved. -/
def keyPointers : List Instr :=
  [.mov .rax (.mem (initial .p)), .alu .add .rax (.mem (initial .pLen)), .store (initial .q) .rax,
    .alu .add .rax (.mem (initial .qLen)), .store (initial .g) .rax,
    .alu .add .rax (.mem (initial .pLen)), .store (initial .y) .rax,
    .alu .add .rax (.mem (initial .pLen)), .store (initial .x) .rax,
    .mov .rdi (.reg .r11)]

/-- Signing has five arguments on the stack, beginning with q_len. -/
def signEntry : List Instr :=
  ([.mov .r11 (.mem (Crt.stk 4))] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .signature) .rax,
    .store (initial .out) .rdi, .store (initial .p) .rdx, .store (initial .pLen) .r8,
    .store (initial .nonce) .r9,
    .mov .rax (.mem (Crt.stk 1)), .store (initial .qLen) .rax,
    .mov .rax (.mem (Crt.stk 2)), .store (initial .digest) .rax,
    .mov .rax (.mem (Crt.stk 3)), .store (initial .digestLen) .rax] : List Instr) ++ keyPointers

/-- Verification has four arguments on the stack, beginning with digest. -/
def verifyEntry : List Instr :=
  ([.mov .r11 (.mem (Crt.stk 3))] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .out) .rax, .store (initial .nonce) .rax,
    .store (initial .p) .rdi, .store (initial .pLen) .rdx, .store (initial .qLen) .rcx,
    .store (initial .signature) .r8,
    .mov .rax (.mem (Crt.stk 1)), .store (initial .digest) .rax,
    .mov .rax (.mem (Crt.stk 2)), .store (initial .digestLen) .rax] : List Instr) ++ keyPointers

/-- The parent workspace's structural header. Its arrays are not used by
Montgomery arithmetic; array zero holds the saved DSA arguments. -/
def parent : List Instr :=
  ([.mov32 .r12 (.imm (BitVec.ofNat 32 outerWords)), .store (hdr sW) .r12,
    .mov32 .rax (.imm 0), .store (hdr sMinv) .rax] : List Instr) ++ setBases

/-- Initialize a child workspace and its odd modulus. This runs only after
the public shape checks; its width is ceil(component_len / 8), at least 3. -/
def child (offset : Nat) (modulus : Operand) : Prog isa := seqs [
  .block (Core.operand arg argLen modulus ++
    ([.mov .rsi (.reg .rdi), .mov .r12 (.mem (hdr argLen)),
      .alu .add .r12 (.imm 7), .shift .shr .r12 3] : List Instr) ++ Core.enter offset ++
    ([.store (hdr sW) .r12, .store (hdr Crt.sLink) .rsi] : List Instr) ++ setBases),
  Arithmetic.load aN arg argLen,
  .block (([.mov .rbx (.mem (hdr (sArr aN))), .mov .rbx (.mem (at0 .rbx))] : List Instr) ++ minv ++
    ([.store (hdr sMinv) .r15, Crt.leave] : List Instr))]

def workspaces : Prog isa := seqs [
  .block parent,
  child pWorkspace ⟨.input .p, .pLen⟩,
  child qWorkspace ⟨.input .q, .qLen⟩]

/-- Copy one computed scalar under the final success mask. When second is
true the destination begins q_len bytes after out. -/
def writeScalar (offset : Nat) (second : Bool) : Prog isa := seqs [
  .block (([.mov .rsi (.reg .rdi), .alu .add .rsi (.imm (BitVec.ofNat 32 offset)),
    .mov .rdx (.mem (Core.field .out)), .mov .rcx (.mem (Core.field .qLen)),
    .mov .r8 (.mem (Core.field .mask))] : List Instr) ++
    (if second then [.alu .add .rdx (.reg .rcx)] else [])),
  .loop (.block [.movzx8 .rax (at0 .rsi), .alu .and .rax (.reg .r8), .store8 (at0 .rdx) .rax,
    .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]) .ne]

/-- Return the success bit and restore the ABI registers. -/
def result : List Instr :=
  ([.mov .rax (.mem (Core.field .mask)), .alu .and .rax (.imm 1)] : List Instr) ++ exit

/-- Early failure on a public, malformed domain must zero the entire
signature without reading uninitialized scalar scratch. -/
def signFailure : Prog isa := seqs [
  .block [.mov .rsi (.mem (Core.field .out)), .mov .rcx (.mem (Core.field .qLen)),
    .alu .add .rcx (.reg .rcx), .mov32 .rax (.imm 0)],
  .loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne,
  .block exit]

def sign (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block signEntry,
  Checks.domainShape,
  .ite .e signFailure (seqs [
    workspaces, Checks.publicKey mul, Checks.privateKey mul,
    Core.sign mul, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true,
    writeScalar r false, writeScalar s true, .block result])]

def verify (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block verifyEntry,
  Checks.domainShape,
  .ite .e (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) (seqs [
    workspaces, Checks.publicKey mul,
    Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
    Core.verify mul, Checks.equal (Core.scalar u) Core.signatureR,
    .block result])]

end VG.Impl.Dsa.X86_64.SignVerify
