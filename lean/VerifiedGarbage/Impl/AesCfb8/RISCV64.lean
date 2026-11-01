module

public import VerifiedGarbage.Impl.AesCbc.RISCV64

/-!
# AES-CFB8: RISC-V implementation

`vg_aes_cfb8_encrypt(schedule = a0, rounds = a1, iv = a2, data = a3, len = a4, scratch = a5)`
and `vg_aes_cfb8_decrypt` with the same arguments (see
`VG.Spec.Cfb8.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` on one block at a time, as on
PPC64LE (`VG.Impl.AesCfb8.PPC64LE`).

They are built from AES-CBC's pieces (`Impl/AesCbc/RISCV64.lean`), whose
arguments are the same but for `len` counting bytes: the registers and the
return address saved in the scratch buffer and the arguments kept in `s1`
(schedule), `s2` (rounds), `s3` (the input block), `s4` (the next byte),
`s5` (bytes left) and `s6` (scratch). Each byte, the input block is copied
to the scratch buffer (at `sv`, where CBC's decryption keeps its block) and
enciphered there, its first byte is XORed into the data byte, and the input
block is shifted left by a byte, with the ciphertext byte (the output when
encrypting, the input when decrypting, in `t1`) shifted in. The contracts
state no alignment for the input block, so it is copied a byte at a time,
and shifted through `sv`: its last 15 bytes copied there, the ciphertext
byte stored after them, and the 16 bytes copied back.

Only the pointers, `rounds` and `len` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCfb8.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov savePtr copy whole encCall chainWrapped)

/-- The input block copied to `sv` (in `t0`), and the arguments of the block
function for it: the schedule, the rounds, the block, `n = 1`, and the
working space. -/
def pre : List Instr :=
  savePtr .s6 ++ copy .t0 .s3 ++
    ([mov .a0 .s1, mov .a1 .s2, mov .a2 .t0, .li .a3 1, mov .a4 .s6] : List Instr)

/-- The input block at `s3` shifted left by a byte, with `t1` (a byte)
shifted in, through the block at `t0`. -/
def shift : List Instr :=
  copyBytes .t3 .s3 .t0 1 0 15 ++ ([.store .b .t1 .t0 15] : List Instr) ++ copy .s3 .t0

/-- On to the next byte. -/
def advance : List Instr := [.addi .s4 .s4 1, .addi .s5 .s5 (-1)]

/-- `C#ⱼ = P#ⱼ ⊕ MSB₈(Oⱼ)`, shifted into the input block. -/
def encPost : List Instr :=
  savePtr .s6 ++
    ([.load .b .t1 .s4 0, .load .b .t2 .t0 0, .logic .xor .t1 .t1 .t2, .store .b .t1 .s4 0] : List Instr) ++
    shift ++ advance

/-- `P#ⱼ = C#ⱼ ⊕ MSB₈(Oⱼ)`, and `C#ⱼ` shifted into the input block. -/
def decPost : List Instr :=
  savePtr .s6 ++
    ([.load .b .t1 .s4 0, .load .b .t2 .t0 0, .logic .xor .t2 .t2 .t1, .store .b .t2 .s4 0] : List Instr) ++
    shift ++ advance

/-- One byte: the input block enciphered in the scratch buffer, and `post`. -/
def body (post : List Instr) : Prog isa := .seq (.block pre) (.seq encCall (.block post))

/-- Each byte, by the CFB8 chain (`Impl.Aes.RISCV64.cfb8Chain`), which
bitslices the round keys once for all the bytes. -/
def encrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfb8EncChainCall

def decrypt : Prog isa := chainWrapped Impl.Aes.RISCV64.cfb8DecChainCall

end VG.Impl.AesCfb8.RISCV64
