import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# XTS-AES: x86-64 implementation

`vg_aes_xts_encrypt(schedule = rdi, rounds = rsi, tweak = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), composed of
calls of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
one block at a time, in place. They are generic over the implementation
they call (`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the tweak),
`r13` (the next block), `r14` (blocks left) and `r15` (scratch). Each
block, the tweak is XORed into the data block, which is enciphered (or
deciphered) in place, the tweak is XORed in again, and the tweak is
multiplied by `α`: its two words, little-endian, shifted left by `add` and
`adc` (carrying the low word's top bit into the high word), and `0x87`
XORed into the low word if the high word's top bit was set, as a mask from
`sbb` of the carry.

Only the pointers, `rounds` and `n` can affect timing.
-/

namespace VG.Impl.AesXts.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (whole xorInto callArgs advance at_)

/-- The tweak at `r12` times `α`. -/
def mulA : List Instr :=
  [.mov .rax (.mem (at_ .r12 0)), .mov .rcx (.mem (at_ .r12 8)), .alu .add .rax (.reg .rax),
   .alu .adc .rcx (.reg .rcx), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 0x87),
   .alu .xor .rax (.reg .rdx), .store (at_ .r12 0) .rax, .store (at_ .r12 8) .rcx]

/-- One block: the tweak XORed in, enciphered (or deciphered) by `b`, the
tweak XORed in again, and the tweak times `α`. -/
def body (b : Blocks) : Prog isa :=
  .seq (.block (xorInto .r13 .r12 ++ callArgs))
    (.seq (.call b.name b.code) (.block (xorInto .r13 .r12 ++ mulA ++ advance)))

def encrypt (b : Blocks) : Prog isa := whole (body b)

def decrypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesXts.X86_64
