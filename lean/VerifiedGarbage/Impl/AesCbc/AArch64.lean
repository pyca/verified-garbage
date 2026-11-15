module

public import VerifiedGarbage.Impl.Aes.AArch64.Callee

/-!
# AES-CBC: AArch64 implementation

`vg_aes_cbc_encrypt(schedule = x0, rounds = x1, iv = x2, data = x3, n = x4, scratch = x5)`
and `vg_aes_cbc_decrypt` with the same arguments (see
`VG.Spec.Cbc.aesEncryptContract` and `aesDecryptContract`), composed of calls
of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks`, in place.
They are generic over the implementation they call (`Blocks`): each is
emitted once for each implementation (e.g. `vg_aes_cbc_encrypt_aes` calls
`vg_aes_encrypt_blocks_aes`).

The scratch buffer (2176 bytes): `[0, 2048)` is the working space of the
block function, `[2048, 2064)` the ciphertext block that decryption keeps
across a call (the last of a group's four), `[2064, 2120)` our caller's
callee-saved registers and our return address `x30`, and `[2120, 2168)` the
first three blocks that a group of decryption keeps across its call. A call
(`bl`) stores nothing in memory, so no stack is used.

Both keep their arguments in `x19` (schedule), `x20` (rounds), `x21` (the
chaining value), `x22` (the next block), `x23` (blocks left) and `x24`
(scratch) across the calls.

* `encrypt`, each block: `Pⱼ ⊕ Cⱼ₋₁` in place, enciphered in place, and
  copied to the chaining value.
* `decrypt`, each group of four blocks while at least four are left
  (`decGroup`): the four `Cⱼ` saved in the scratch buffer (the first three
  at `gOff`, the fourth at `cOff`), deciphered in place by one call (as many
  blocks as the bitsliced block function deciphers at once, which bitslices
  the round keys once for the call), each XORed with `Cⱼ₋₁` (the chaining
  value for the first, the saved block before it for the others), and the
  last saved `Cⱼ` copied to the chaining value; then each block left
  (`decBody`): `Cⱼ` saved at `cOff`, deciphered in place, XORed with the
  chaining value, and the saved `Cⱼ` copied to the chaining value.

The model has no flags: the branches are `cbz`/`cbnz` on the blocks left,
and on `x9`, which `few` sets to one when fewer than four are left (the sign
of the blocks left less four: there are fewer than `2⁶⁰` blocks).
Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCbc.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)

/-- `mov d, n`. -/
def mov (d n : Reg) : Instr := .addImm .x d n 0

/-- The offset of the saved ciphertext block in the scratch buffer. -/
def cOff : Nat := 2048

/-- The registers saved in the scratch buffer, and where (`x24`, the base of
the restore, last). -/
def saved : List (Reg × Nat) :=
  [(.x19, 2064), (.x20, 2072), (.x21, 2080), (.x22, 2088), (.x23, 2096), (.x30, 2104), (.x24, 2112)]

def save : List Instr := saved.map fun (r, d) => .str .x r .x5 d

/-- Restores the registers, with `x24` (restored last) the scratch buffer. -/
def restore : List Instr := saved.map fun (r, d) => .ldr .x r .x24 d

/-- The arguments to their registers. -/
def setup : List Instr :=
  [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, mov .x24 .x5]

/-- The arguments of the block function for the block at `x22`: the
schedule, the rounds, the block, `n = 1`, and the working space. -/
def callArgs : List Instr := [mov .x0 .x19, mov .x1 .x20, mov .x2 .x22, .movz .x .x3 1 0, mov .x4 .x24]

/-- The block at `x22` XORed with the chaining value at `x21`, in place. -/
def xorInto : List Instr :=
  [.ldr .x .x9 .x22 0, .ldr .x .x10 .x21 0, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x22 0,
   .ldr .x .x9 .x22 8, .ldr .x .x10 .x21 8, .logic .eor .x .x9 .x9 .x10, .str .x .x9 .x22 8]

/-- The block at `src + s` copied to `dst + d`. -/
def copy (dst : Reg) (d : Nat) (src : Reg) (s : Nat) : List Instr :=
  [.ldr .x .x9 src s, .str .x .x9 dst d, .ldr .x .x9 src (s + 8), .str .x .x9 dst (d + 8)]

/-- On to the next block. -/
def advance : List Instr := [.addImm .x .x22 .x22 16, .subImm .x .x23 .x23 1]

/-- The registers saved and the arguments set up, `body` run once for each
block, and the registers restored. -/
def whole (body : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .x .x23) (.block []) (.loop body (.nonzero .x .x23))) (.block restore))

/-! ## `vg_aes_cbc_encrypt` -/

/-- One block: `Pⱼ ⊕ Cⱼ₋₁`, enciphered, and the result the chaining value. -/
def encBody (b : Blocks) : Prog isa :=
  .seq (.block (xorInto ++ callArgs)) (.seq (.call b.name b.code) (.block (copy .x21 0 .x22 0 ++ advance)))

def encrypt (b : Blocks) : Prog isa := whole (encBody b)

/-! ## `vg_aes_cbc_decrypt` -/

/-- One block: `Cⱼ` saved, deciphered, XORed with `Cⱼ₋₁`, and the saved
`Cⱼ` the chaining value. -/
def decBody (b : Blocks) : Prog isa :=
  .seq (.block (copy .x24 cOff .x22 0 ++ callArgs))
    (.seq (.call b.name b.code) (.block (xorInto ++ copy .x21 0 .x24 cOff ++ advance)))

/-! ## Groups of four blocks -/

/-- The offset of the first three blocks a group keeps in the scratch buffer
(the fourth is kept at `cOff`). -/
def gOff : Nat := 2120

/-- The block at `src + e` XORed into the block at `dst + d`. -/
def xorAt (dst : Reg) (d : Nat) (src : Reg) (e : Nat) : List Instr :=
  [.ldr .x .x9 dst d, .ldr .x .x10 src e, .logic .eor .x .x9 .x9 .x10, .str .x .x9 dst d,
   .ldr .x .x9 dst (d + 8), .ldr .x .x10 src (e + 8), .logic .eor .x .x9 .x9 .x10, .str .x .x9 dst (d + 8)]

/-- `x9` is one if fewer than four blocks are left, and zero otherwise. -/
def few : List Instr := [.subImm .x .x9 .x23 4, .lsr .x .x9 .x9 63]

/-- On to the block after the four (`x9` is one if fewer than four are left). -/
def advance4 : List Instr := [.addImm .x .x22 .x22 64, .subImm .x .x23 .x23 4] ++ few

/-- `group` while at least four blocks are left, then `one` for each block
left. -/
def groups (group one : Prog isa) : Prog isa :=
  .seq (.block few)
    (.seq (.ite (.nonzero .x .x9) (.block []) (.loop group (.zero .x .x9)))
      (.ite (.zero .x .x23) (.block []) (.loop one (.nonzero .x .x23))))

/-- The registers saved and the arguments set up, `groups group one`, and
the registers restored. -/
def batched (group one : Prog isa) : Prog isa :=
  .seq (.block (save ++ setup))
    (.seq (.ite (.zero .x .x23) (.block []) (groups group one)) (.block restore))

/-- Block `j` of the four at `x22` saved in slot `j` at `gOff`. -/
def saveAt (j : Nat) : List Instr := copy .x24 (gOff + 16 * j) .x22 (16 * j)

/-- The four blocks at `x22` saved: the first three at `gOff`, the fourth at
`cOff`. -/
def decSave : List Instr := saveAt 0 ++ saveAt 1 ++ saveAt 2 ++ copy .x24 cOff .x22 48

/-- The arguments of the block function for the four blocks at `x22`. -/
def callArgs4 : List Instr := [mov .x0 .x19, mov .x1 .x20, mov .x2 .x22, .movz .x .x3 4 0, mov .x4 .x24]

/-- Deciphered block `j + 1` XORed with the saved block `j`. -/
def fixAt (j : Nat) : List Instr := xorAt .x22 (16 * (j + 1)) .x24 (gOff + 16 * j)

/-- Each deciphered block XORed with `Cⱼ₋₁` (the chaining value for the
first), and the last saved `Cⱼ` the chaining value. -/
def decFix : List Instr := xorInto ++ fixAt 0 ++ fixAt 1 ++ fixAt 2 ++ copy .x21 0 .x24 cOff

/-- Four blocks: saved, deciphered by one call, and fixed up. -/
def decGroup (b : Blocks) : Prog isa :=
  .seq (.block (decSave ++ callArgs4)) (.seq (.call b.name b.code) (.block (decFix ++ advance4)))

def decrypt (b : Blocks) : Prog isa := batched (decGroup b) (decBody b)

end VG.Impl.AesCbc.AArch64
