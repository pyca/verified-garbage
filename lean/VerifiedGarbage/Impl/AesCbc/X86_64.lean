import VerifiedGarbage.Impl.Aes.X86_64.Callee

/-!
# AES-CBC: x86-64 implementation

`vg_aes_cbc_encrypt(schedule = rdi, rounds = rsi, iv = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), composed of calls
of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on one
block at a time, in place. They are generic over the implementation they call
(`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_cbc_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function, `[2048, 2064)` the ciphertext block that decryption keeps
across the call, and `[2064, 2112)` our caller's callee-saved registers.

Both keep their arguments in `rbx` (schedule), `rbp` (rounds), `r12` (the
chaining value), `r13` (the next block), `r14` (blocks left) and `r15`
(scratch) across the calls.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each block: `Cⱼ` saved in the scratch buffer, deciphered in
  place, XORed with the chaining value `Cⱼ₋₁`, and the saved `Cⱼ` copied to
  the chaining value.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesCbc.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)

def at_ (b : Reg) (d : Nat) : MemOp := { base := b, disp := d }

/-- The offset of the saved ciphertext block in the scratch buffer. -/
def cOff : Nat := 2048

def saved : List (Reg × Nat) :=
  [(.rbx, 2064), (.rbp, 2072), (.r12, 2080), (.r13, 2088), (.r14, 2096), (.r15, 2104)]

def save : List Instr := saved.map fun (r, d) => .store (at_ .r9 d) r

/-- Restores the registers, with `r15` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .mov r (.mem (at_ .r15 d))

/-- The arguments to their registers; ZF is set if there are no blocks. -/
def setup : List Instr :=
  [.mov .rbx (.reg .rdi), .mov .rbp (.reg .rsi), .mov .r12 (.reg .rdx), .mov .r13 (.reg .rcx),
   .mov .r14 (.reg .r8), .mov .r15 (.reg .r9), .alu .test .r14 (.reg .r14)]

/-- The arguments of the block function for the block at `r13`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def callArgs : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r13), .mov32 .rcx (.imm 1),
   .mov .r8 (.reg .r15)]

/-- The block at `dst` XORed with the block at `src`, in place. -/
def xorInto (dst src : Reg) : List Instr :=
  [.mov .rax (.mem (at_ dst 0)), .alu .xor .rax (.mem (at_ src 0)), .store (at_ dst 0) .rax,
   .mov .rax (.mem (at_ dst 8)), .alu .xor .rax (.mem (at_ src 8)), .store (at_ dst 8) .rax]

/-- The block at `src + s` copied to `dst + d`. -/
def copy (dst : Reg) (d : Nat) (src : Reg) (s : Nat) : List Instr :=
  [.mov .rax (.mem (at_ src s)), .store (at_ dst d) .rax,
   .mov .rax (.mem (at_ src (s + 8))), .store (at_ dst (d + 8)) .rax]

/-- On to the next block (ZF is set when none are left). -/
def advance : List Instr := [.alu .add .r13 (.imm 16), .alu .sub .r14 (.imm 1)]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .e (.block []) (.loop body .ne)) (.block restore))

/-! ## `vg_aes_cbc_encrypt` -/

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody (b : Blocks) : Prog isa :=
  .seq (.block (xorInto .r13 .r12 ++ callArgs))
    (.seq (.call b.name b.code) (.block (copy .r12 0 .r13 0 ++ advance)))

def encrypt (b : Blocks) : Prog isa := whole (encBody b)

/-! ## `vg_aes_cbc_decrypt` -/

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved
`Cⱼ` the chaining value. -/
def decBody (b : Blocks) : Prog isa :=
  .seq (.block (copy .r15 cOff .r13 0 ++ callArgs))
    (.seq (.call b.name b.code) (.block (xorInto .r13 .r12 ++ copy .r12 0 .r15 cOff ++ advance)))

def decrypt (b : Blocks) : Prog isa := whole (decBody b)

end VG.Impl.AesCbc.X86_64
