module

public import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# XTS-AES: x86-64 implementation

`vg_aes_xts_encrypt(schedule = rdi, rounds = rsi, tweak = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), composed of one
call of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
all the blocks, in place. They are generic over the implementation they call
(`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the tweak),
`r13` (the next block), `r14` (blocks left) and `r15` (scratch). The tweak
`T` is saved at `scratch + 2048`; a pass over the blocks XORs each block's
tweak into it, multiplying the tweak by `α` after each (`pass`); `T` is
restored, the block function enciphers (or deciphers) all the blocks in
place, and a second pass XORs the tweaks in again, leaving the tweak after
the last block. The first pass keeps the data pointer and the number of
blocks in `r10` and `r11`. The tweak is multiplied by `α` as its two words,
little-endian, shifted left by `add` and `adc` (carrying the low word's top
bit into the high word), and `0x87` XORed into the low word if the high
word's top bit was set, as a mask from `sbb` of the carry.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (save setup restore xorInto copy cOff advance at_)

/-- The tweak at `r12` times `α`. -/
def mulA : List Instr :=
  [.mov .rax (.mem (at_ .r12 0)), .mov .rcx (.mem (at_ .r12 8)), .alu .add .rax (.reg .rax),
   .alu .adc .rcx (.reg .rcx), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 0x87),
   .alu .xor .rax (.reg .rdx), .store (at_ .r12 0) .rax, .store (at_ .r12 8) .rcx]

/-- One block: the tweak XORed in, and the tweak times `α`. -/
def passBody : List Instr := xorInto .r13 .r12 ++ mulA ++ advance

/-- Each block from `r13` on (`r14` of them, at least one) with its tweak
XORed in. -/
def pass : Prog isa := .loop (.block passBody) .ne

/-- `T` saved, and the data pointer and number of blocks kept. -/
def saveT : List Instr := copy .r15 cOff .r12 0 ++ ([.mov .r10 (.reg .r13), .mov .r11 (.reg .r14)] : List Instr)

/-- The data pointer and number of blocks back, `T` restored, and the
arguments of the block function on all the blocks. -/
def callArgs : List Instr :=
  ([.mov .r13 (.reg .r10), .mov .r14 (.reg .r11)] : List Instr) ++ copy .r12 0 .r15 cOff ++
  ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r13), .mov .rcx (.reg .r14),
   .mov .r8 (.reg .r15)] : List Instr)

/-- The blocks (at least one): the tweaks XORed in, enciphered (or
deciphered) by `b`, and the tweaks XORed in again. -/
def batch (b : Blocks) : Prog isa :=
  .seq (.block saveT) (.seq pass (.seq (.block callArgs) (.seq (.call b.name b.code) pass)))

def crypt (b : Blocks) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .e (.block []) (batch b)) (.block restore))

def encrypt (b : Blocks) : Prog isa := crypt b

def decrypt (b : Blocks) : Prog isa := crypt b

end VG.Impl.AesXts.X86_64
