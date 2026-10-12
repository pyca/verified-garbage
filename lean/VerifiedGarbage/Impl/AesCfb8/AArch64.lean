module

public import VerifiedGarbage.Impl.AesCbc.AArch64

/-!
# AES-CFB8: AArch64 implementation

`vg_aes_cfb8_encrypt(schedule = x0, rounds = x1, iv = x2, data = x3, len = x4, scratch = x5)`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time. They
are generic over the implementation they call (`Blocks`): each is emitted
once for each implementation (e.g. `vg_aes_cfb8_encrypt_aes` calls
`vg_aes_encrypt_blocks_aes`).

They are built from AES-CBC's pieces (`Impl/AesCbc/AArch64.lean`), whose
arguments are the same but for `len` counting bytes: the registers saved in
the scratch buffer and the arguments kept in `x19` (schedule), `x20`
(rounds), `x21` (the input block), `x22` (the next byte), `x23` (bytes left)
and `x24` (scratch). Each byte, the input block is copied to the scratch
buffer (at `cOff`) and enciphered there, its first byte is XORed into the
data byte, and the input block is shifted left by a byte (two `extr`), with
the ciphertext byte (the output when encrypting, the input when decrypting,
in `x9`) shifted in.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.AArch64

open VG.AArch64
open VG.Impl.Aes.AArch64 (Blocks)
open VG.Impl.AesCbc.AArch64 (mov cOff copy whole)

/-- The input block copied to `x24 + cOff`, and the arguments of the block
function for it: the schedule, the rounds, the block, `n = 1`, and the
working space. -/
def pre : List Instr :=
  copy .x24 cOff .x21 0 ++ [mov .x0 .x19, mov .x1 .x20, .addImm .x .x2 .x24 2048, .movz .x .x3 1 0, mov .x4 .x24]

/-- The input block at `x21` shifted left by a byte, with the low byte of
`x9` shifted in. -/
def shift : List Instr :=
  [.ldr .x .x10 .x21 0, .ldr .x .x11 .x21 8, .extr .x .x12 .x11 .x10 8, .extr .x .x13 .x9 .x11 8,
   .str .x .x12 .x21 0, .str .x .x13 .x21 8]

/-- On to the next byte. -/
def advance : List Instr := [.addImm .x .x22 .x22 1, .subImm .x .x23 .x23 1]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  ([.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x9 .x9 .x10, .strb .x9 .x22 0] : List Instr) ++ shift ++ advance

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  ([.ldrb .x9 .x22 0, .ldrb .x10 .x24 cOff, .logic .eor .x .x10 .x10 .x9, .strb .x10 .x22 0] : List Instr) ++ shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (b : Blocks) (post : List Instr) : Prog isa :=
  .seq (.block pre) (.seq (.call b.name b.code) (.block post))

def encrypt (b : Blocks) : Prog isa := whole (body b encPost)

def decrypt (b : Blocks) : Prog isa := whole (body b decPost)

end VG.Impl.AesCfb8.AArch64
