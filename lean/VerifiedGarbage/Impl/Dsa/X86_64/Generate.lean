module

public import VerifiedGarbage.Impl.Dsa.X86_64.SignVerify

/-!
# DSA domain checks and key derivation on x86-64

`checkParameters` is `vg_dsa_check_parameters`, `deriveKey` is
`vg_dsa_derive_key` (Spec/Dsa/Derive.lean). Both reuse the signer's
workspace and its checks of the domain and the public value
(`Checks.signingKey`): checking parameters points the public value at g,
whose checks it repeats; deriving a key computes y = g^x, copies it past the
signer's layout (`derivedY`), where the checks read it as an input, and
checks x's range. The derived key is written under the final mask.
-/

@[expose] public section

namespace VG.Impl.Dsa.X86_64.Generate

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Impl.Rsa.X86_64 VG.Impl.Dsa.Layout SignVerify

/-- `vg_dsa_check_parameters(params, params_len, p_len, q_len, scratch,
scratch_len)`: all arguments in registers. The public value is g, and
there is no digest. -/
def checkEntry : List Instr :=
  ([.mov .r11 (.reg .r8)] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .signature) .rax, .store (initial .out) .rax,
    .store (initial .nonce) .rax, .store (initial .digest) .rax, .store (initial .digestLen) .rax,
    .store (initial .p) .rdi, .store (initial .pLen) .rdx, .store (initial .qLen) .rcx] : List Instr) ++
  keyPointers ++ ([.mov .rax (.mem (initial .g)), .store (initial .y) .rax] : List Instr)

/-- `vg_dsa_derive_key(out, out_len, params, params_len, p_len, x, q_len,
scratch, scratch_len)`: three arguments on the stack, beginning with q_len.
x is the supplied scalar and y the derived value's slot. -/
def deriveEntry : List Instr :=
  ([.mov .r11 (.mem (Crt.stk 2))] : List Instr) ++ save ++
  ([.mov32 .rax (.imm 0), .store (initial .signature) .rax, .store (initial .nonce) .rax,
    .store (initial .digest) .rax, .store (initial .digestLen) .rax,
    .store (initial .out) .rdi, .store (initial .p) .rdx, .store (initial .pLen) .r8,
    .mov .rax (.mem (Crt.stk 1)), .store (initial .qLen) .rax] : List Instr) ++
  keyPointers ++
  ([.store (initial .x) .r9, .mov .rax (.reg .r11), .alu .add .rax (.imm (BitVec.ofNat 32 derivedY)),
    .store (initial .y) .rax] : List Instr)

/-- Copy `rcx` bytes from `rsi` to `rdx` under the mask in `r8`. -/
def copyMasked : Prog isa :=
  .loop (.block [.movzx8 .rax (at0 .rsi), .alu .and .rax (.reg .r8), .store8 (at0 .rdx) .rax,
    .alu .add .rsi (.imm 1), .alu .add .rdx (.imm 1), .alu .sub .rcx (.imm 1)]) .ne

/-- Copy the computed y past the signer's layout. -/
def copyY : Prog isa := seqs [
  .block [.mov .rsi (.reg .rdi), .alu .add .rsi (.imm (BitVec.ofNat 32 t2)),
    .mov .rdx (.reg .rdi), .alu .add .rdx (.imm (BitVec.ofNat 32 derivedY)),
    .mov .rcx (.mem (Core.field .pLen)), .mov .r8 (.imm (-1))],
  copyMasked]

/-- Load the key's addresses and widths once: out in r13, y in r9, x in r10,
p_len in r11 and q_len in r12; the copies then compute every address from
registers. -/
def keyHead : List Instr :=
  [.mov .r8 (.mem (Core.field .mask)), .mov .r13 (.mem (Core.field .out)),
    .mov .r9 (.mem (Core.field .y)), .mov .r10 (.mem (Core.field .x)),
    .mov .r11 (.mem (Core.field .pLen)), .mov .r12 (.mem (Core.field .qLen)),
    .mov .rdx (.reg .r13), .mov .rsi (.mem (Core.field .p)), .mov .rcx (.reg .r11),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.reg .r12)]

/-- Write p||q||g||y||x under the final mask: the packed domain as given,
then y and x. -/
def writeKey : Prog isa := seqs [
  .block keyHead,
  copyMasked,
  .block [.mov .rdx (.reg .r13), .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r11),
    .alu .add .rdx (.reg .r12), .mov .rsi (.reg .r9), .mov .rcx (.reg .r11)],
  copyMasked,
  .block [.mov .rdx (.reg .r13), .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r11),
    .alu .add .rdx (.reg .r11), .alu .add .rdx (.reg .r12), .mov .rsi (.reg .r10), .mov .rcx (.reg .r12)],
  copyMasked]

/-- A malformed domain zeros the whole key, 3*p_len + 2*q_len bytes. -/
def deriveFailure : Prog isa := seqs [
  .block [.mov .rsi (.mem (Core.field .out)), .mov .rcx (.mem (Core.field .pLen)),
    .alu .add .rcx (.reg .rcx), .alu .add .rcx (.mem (Core.field .pLen)),
    .alu .add .rcx (.mem (Core.field .qLen)), .alu .add .rcx (.mem (Core.field .qLen)),
    .mov32 .rax (.imm 0)],
  .loop (.block [.store8 (at0 .rsi) .rax, .alu .add .rsi (.imm 1), .alu .sub .rcx (.imm 1)]) .ne,
  .block exit]

def checkParameters (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block checkEntry,
  Checks.domainShape,
  .ite .e (.block (([.mov32 .rax (.imm 0)] : List Instr) ++ exit)) (seqs [
    workspaces, Checks.signingKey sq mul, .block result])]

def deriveKey (sq : Prog isa) (mul : Nat → Nat → Nat → Prog isa) : Prog isa := seqs [
  .block deriveEntry,
  Checks.domainShape,
  .ite .e deriveFailure (seqs [
    workspaces, Checks.range qWorkspace Core.privateScalar,
    Core.pow sq mul pWorkspace Core.generator Core.privateScalar (Core.element t2),
    copyY, Checks.signingKey sq mul, writeKey, .block result])]

end VG.Impl.Dsa.X86_64.Generate
