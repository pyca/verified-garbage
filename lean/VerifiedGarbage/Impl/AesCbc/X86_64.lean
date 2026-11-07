module

public import VerifiedGarbage.Impl.Aes.X86_64.Callee

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
across the call, `[2064, 2112)` our caller's callee-saved registers, and
`[2112, 2176)` the four blocks that a group of decryption keeps across its
call (AES-CFB128's, `Impl/AesCfb/X86_64.lean`, the inputs of its call).

Both keep their arguments in `rbx` (schedule), `rbp` (rounds), `r12` (the
chaining value), `r13` (the next block), `r14` (blocks left) and `r15`
(scratch) across the calls.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each group of four blocks while at least four are left
  (`decGroup`): the four `Cⱼ` saved in the scratch buffer at `[2112, 2176)`
  (`gOff`), deciphered in place by one call (as many blocks as the
  bitsliced block function deciphers at once, which bitslices the round
  keys once for the call), each XORed with `Cⱼ₋₁` (the chaining value for
  the first, the saved block before it for the others), and the last saved
  `Cⱼ` copied to the chaining value; then each block left (`decBody`): `Cⱼ`
  saved at `cOff`, deciphered in place, XORed with the chaining value, and
  the saved `Cⱼ` copied to the chaining value.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

@[expose] public section

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

/-! ## Groups of four blocks -/

/-- The offset of the four blocks a group keeps in the scratch buffer. -/
def gOff : Nat := 2112

/-- The block at `src + e` XORed into the block at `dst + d`. -/
def xorAt (dst : Reg) (d : Nat) (src : Reg) (e : Nat) : List Instr :=
  [.mov .rax (.mem (at_ dst d)), .alu .xor .rax (.mem (at_ src e)), .store (at_ dst d) .rax,
   .mov .rax (.mem (at_ dst (d + 8))), .alu .xor .rax (.mem (at_ src (e + 8))), .store (at_ dst (d + 8)) .rax]

/-- On to the block after the four (CF is set when fewer than four are left). -/
def advance4 : List Instr := [.alu .add .r13 (.imm 64), .alu .sub .r14 (.imm 4), .alu .cmp .r14 (.imm 4)]

/-- `group` while at least four blocks are left, then `one` for each block
left (`r14` is not zero on entry). -/
def groups (group one : Prog isa) : Prog isa :=
  .seq (.block [.alu .cmp .r14 (.imm 4)])
    (.seq (.ite .b (.block []) (.loop group .ae))
      (.seq (.block [.alu .test .r14 (.reg .r14)]) (.ite .e (.block []) (.loop one .ne))))

/-- The registers saved and the arguments set up, `groups group one`, and
the registers restored. -/
def batched (group one : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .e (.block []) (groups group one)) (.block restore))

/-- Block `j` of the four at `r13` saved in slot `j` at `gOff`. -/
def saveAt (j : Nat) : List Instr := copy .r15 (gOff + 16 * j) .r13 (16 * j)

/-- The four blocks at `r13` saved at `gOff`. -/
def decSave : List Instr := saveAt 0 ++ saveAt 1 ++ saveAt 2 ++ saveAt 3

/-- The arguments of the block function for the four blocks at `r13`. -/
def callArgs4 : List Instr :=
  [.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r13), .mov32 .rcx (.imm 4),
   .mov .r8 (.reg .r15)]

/-- Deciphered block `j + 1` XORed with the saved block `j`. -/
def fixAt (j : Nat) : List Instr := xorAt .r13 (16 * (j + 1)) .r15 (gOff + 16 * j)

/-- Each deciphered block XORed with `Cⱼ₋₁` (the chaining value for the
first), and the last saved `Cⱼ` the chaining value. -/
def decFix : List Instr :=
  xorAt .r13 0 .r12 0 ++ fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ copy .r12 0 .r15 (gOff + 16 * 3)

/-- Four blocks: saved, deciphered by one call, and fixed up. -/
def decGroup (b : Blocks) : Prog isa :=
  .seq (.block (decSave ++ callArgs4)) (.seq (.call b.name b.code) (.block (decFix ++ advance4)))

def decrypt (b : Blocks) : Prog isa := batched (decGroup b) (decBody b)

end VG.Impl.AesCbc.X86_64
