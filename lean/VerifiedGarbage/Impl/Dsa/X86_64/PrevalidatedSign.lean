module

public import VerifiedGarbage.Impl.Dsa.X86_64.Generate

/-!
# Separate reusable private-key validation from DSA signing on x86-64

`validate` is `vg_dsa_validate_private_key` (Spec/Dsa/PrevalidatedSign.lean):
the domain check's register entry (`Generate.checkEntry`), with the nonce
field pointing at x, so that the signer's key checks (`Checks.signingKey`
and `Checks.privateKey`, whose nonce range check is then x's) are every
check signing makes of the key. `sign` is one signing attempt of
`vg_dsa_sign_random_prevalidated`: the signer's program with those two
checks, and their two exponentiations, replaced by rebuilding q−2 and the
nonce's range check; the precondition that the exact key bytes validate
makes the omitted checks' mask true.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.PrevalidatedSign

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout VG.Impl.Dsa.X86_64.SignVerify

/-- `vg_dsa_validate_private_key(key, key_len, p_len, q_len, scratch,
scratch_len)`: all arguments in registers, as the domain check's. The
nonce field points at x. -/
def validateEntry : List Instr :=
  ([.mov .r11 (.reg .r8)] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .signature) .rax, .store (initial .out) .rax,
    .store (initial .nonce) .rax, .store (initial .digest) .rax, .store (initial .digestLen) .rax,
    .store (initial .p) .rdi, .store (initial .pLen) .rdx, .store (initial .qLen) .rcx] : List Instr) ++
  keyPointers ++ ([.mov .rax (.mem (initial .x)), .store (initial .nonce) .rax] : List Instr)

def validate (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block validateEntry,
  Checks.domainShape,
  .ite .e (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) (seqs [
    workspaces, Checks.signingKey sq mul, Checks.privateKey sq mul, .block result])]

/-- Rebuild q−2 in this call's workspace and check the nonce's range;
validation is a precondition on the immutable key bytes, never a flag
recovered from scratch. -/
def compute (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  Checks.modulusMinus qWorkspace 2 (Core.scalar qMinusTwo),
  Checks.range qWorkspace Core.nonce,
  Core.sign sq mul, Checks.zero (Core.scalar r) true, Checks.zero (Core.scalar s) true]

def sign (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block signEntry,
  Checks.domainShape,
  .ite .e signFailure (seqs [
    workspaces, compute sq mul,
    writeScalar r false, writeScalar s true, .block result])]

end VG.Impl.Dsa.X86_64.PrevalidatedSign
