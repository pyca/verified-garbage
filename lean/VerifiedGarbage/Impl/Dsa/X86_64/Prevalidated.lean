module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify

/-! # Separate reusable public-key validation from DSA signature verification on x86-64 -/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Prevalidated

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64.SignVerify

/-- Six register arguments: key, key length, p length, q length, scratch,
scratch length. The fields are verification's, with no digest; the
signature field holds the scratch pointer, which validation never reads. -/
def validateEntry : List Instr :=
  ([.mov .r11 (.reg .r8)] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .out) .rax, .store (initial .nonce) .rax,
    .store (initial .p) .rdi, .store (initial .pLen) .rdx, .store (initial .qLen) .rcx,
    .store (initial .signature) .r8,
    .store (initial .digest) .rax, .store (initial .digestLen) .rax] : List Instr) ++ keyPointers

def validate (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block validateEntry,
  Checks.domainShape,
  .ite .e (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) (seqs [
    workspaces, Checks.publicKey sq mul, .block result])]

/-- Rebuild q−2 in this call's workspace; validation is a precondition on the
immutable key bytes, never a flag recovered from scratch. -/
def compute (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo),
  Checks.range qWorkspace Core.signatureR, Checks.range qWorkspace Core.signatureS,
  Core.verify sq mul, Checks.equal (Core.scalar u) Core.signatureR]

def verify (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block verifyEntry,
  Checks.domainShape,
  .ite .e (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) (seqs [
    workspaces, compute sq mul, .block result])]

end VG.Impl.Dsa.X86_64.Prevalidated
