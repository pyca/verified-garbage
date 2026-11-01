module

public import VerifiedGarbage.Impl.AesCbc.X86_64

/-!
# XTS-AES: x86-64 implementation

`vg_aes_xts_encrypt(schedule = rdi, rounds = rsi, tweak = rdx, data = rcx, n = r8, scratch = r9)`
and `vg_aes_xts_decrypt` with the same arguments (see
`VG.Proof.Xts.aesEncryptContract` and `aesDecryptContract`), composed of one
call of the verified `vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on
all the blocks, in place. They are generic over the implementation they call
(`Blocks`): each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86_64.lean`), whose
arguments are the same: the registers saved in the scratch buffer and the
arguments kept in `rbx` (schedule), `rbp` (rounds), `r12` (the tweak),
`r13` (the next block), `r14` (blocks left) and `r15` (scratch). A pass over
the blocks loads the tweak `T` into `rax` (low word) and `rcx` (high word),
XORs each block's tweak into it and multiplies the tweak by `α` after each
(`pass`), in registers, leaving `T` in memory unchanged; the block function
enciphers (or deciphers) all the blocks in place, and a second pass XORs the
tweaks in again and stores the tweak after the last block (`stT`). The first
pass keeps the data pointer and the number of blocks in `r10` and `r11`. The
tweak is multiplied by `α` as its two words, little-endian: `0x87` as a mask
from the high word's top bit (`add` of the word to itself carries it out, and
`sbb` spreads it), then the words shifted left by `add` and `adc` (carrying
the low word's top bit into the high word), and the mask XORed into the low
word. Keeping the tweak in registers leaves a chain of a few cycles from one
block's tweak to the next, rather than a store and a load of it in memory.

Only the pointers, `rounds` and `n` can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesXts.X86_64

open VG.X86_64
open VG.Impl.Aes.X86_64 (Blocks)
open VG.Impl.AesCbc.X86_64 (save setup restore advance at_)

/-- The tweak at `r12` loaded: the low word into `rax`, the high word into
`rcx`. -/
def ldT : List Instr := [.mov .rax (.mem (at_ .r12 0)), .mov .rcx (.mem (at_ .r12 8))]

/-- The tweak in `rax` and `rcx` stored at `r12`. -/
def stT : List Instr := [.store (at_ .r12 0) .rax, .store (at_ .r12 8) .rcx]

/-- The tweak in `rax` and `rcx` XORed into the block at `r13`. -/
def xorT : List Instr :=
  [.mov .rdx (.mem (at_ .r13 0)), .alu .xor .rdx (.reg .rax), .store (at_ .r13 0) .rdx,
   .mov .rdx (.mem (at_ .r13 8)), .alu .xor .rdx (.reg .rcx), .store (at_ .r13 8) .rdx]

/-- The tweak in `rax` and `rcx` times `α`. -/
def mulA : List Instr :=
  [.mov .rdx (.reg .rcx), .alu .add .rdx (.reg .rdx), .alu .sbb .rdx (.reg .rdx), .alu .and .rdx (.imm 0x87),
   .alu .add .rax (.reg .rax), .alu .adc .rcx (.reg .rcx), .alu .xor .rax (.reg .rdx)]

/-- One block: the tweak XORed in, and the tweak times `α`. -/
def passBody : List Instr := xorT ++ mulA ++ advance

/-- Each block from `r13` on (`r14` of them, at least one) with its tweak
XORed in, from the tweak at `r12`, which is left unchanged; the tweak after
the last block is left in `rax` and `rcx`. -/
def pass : Prog isa := .seq (.block ldT) (.loop (.block passBody) .ne)

/-- The data pointer and number of blocks kept. -/
def saveT : List Instr := [.mov .r10 (.reg .r13), .mov .r11 (.reg .r14)]

/-- The data pointer and number of blocks back, and the arguments of the
block function on all the blocks. -/
def callArgs : List Instr :=
  ([.mov .r13 (.reg .r10), .mov .r14 (.reg .r11)] : List Instr) ++
  ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .rbp), .mov .rdx (.reg .r13), .mov .rcx (.reg .r14),
   .mov .r8 (.reg .r15)] : List Instr)

/-- The blocks (at least one): the tweaks XORed in, enciphered (or
deciphered) by `b`, the tweaks XORed in again, and the tweak after the last
block stored. -/
def batch (b : Blocks) : Prog isa :=
  .seq (.block saveT) (.seq pass (.seq (.block callArgs) (.seq (.call b.name b.code) (.seq pass (.block stT)))))

def crypt (b : Blocks) : Prog isa :=
  .seq (.block (save ++ setup)) (.seq (.ite .e (.block []) (batch b)) (.block restore))

def encrypt (b : Blocks) : Prog isa := crypt b

def decrypt (b : Blocks) : Prog isa := crypt b

end VG.Impl.AesXts.X86_64
