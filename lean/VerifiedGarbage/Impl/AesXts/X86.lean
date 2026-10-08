import VerifiedGarbage.Impl.AesCbc.X86

/-!
# XTS-AES: x86 (32-bit) implementation

`vg_aes_xts_encrypt(schedule, rounds, tweak, data, n, scratch)` and
`vg_aes_xts_decrypt` with the same arguments (see
`VG.Spec.Xts.aesEncryptContract` and `aesDecryptContract`), every argument
on the stack (cdecl), composed of calls of the verified
`vg_aes_encrypt_blocks` or `vg_aes_decrypt_blocks` on one block at a time,
in place. They are generic over the implementation they call (`Blocks`):
each is emitted once for each implementation (e.g.
`vg_aes_xts_encrypt_aesni` calls `vg_aes_encrypt_blocks_aesni`).

They are built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose
arguments are in the same places: `esi` points at the next block, and the
other arguments are reloaded from the stack. Each block, the tweak is XORed
into the data block, which is enciphered (or deciphered) in place, the
tweak is XORed in again, and the tweak is multiplied by `α`: its four
words, little-endian, shifted left by `add` and `adc` (carrying each word's
top bit into the next), and `0x87` XORed into the first word if the last
word's top bit was set, as a mask from `sbb` of the carry.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesXts.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4)
open VG.Impl.AesCbc.X86 (whole blkCall callArgs)

/-- The tweak at `ebx` times `α`. -/
def mulA : List Instr :=
  [.mov .eax (.mem (at_ .ebx 0)), .mov .ecx (.mem (at_ .ebx 4)), .mov .edx (.mem (at_ .ebx 8)),
   .mov .edi (.mem (at_ .ebx 12)), .alu .add .eax (.reg .eax), .alu .adc .ecx (.reg .ecx),
   .alu .adc .edx (.reg .edx), .alu .adc .edi (.reg .edi), .alu .sbb .ebp (.reg .ebp),
   .alu .and .ebp (.imm 0x87), .alu .xor .eax (.reg .ebp), .store (at_ .ebx 0) .eax,
   .store (at_ .ebx 4) .ecx, .store (at_ .ebx 8) .edx, .store (at_ .ebx 12) .edi]

/-- The tweak XORed into the data block, and the arguments of the call. -/
def pre : List Instr := [.mov .ebx (argOp 2)] ++ xor4 .esi .ebx .esi 0 0 0 ++ callArgs

/-- The tweak XORed in again, the tweak times `α`, and on to the next block. -/
def post : List Instr := [.mov .ebx (argOp 2)] ++ xor4 .esi .ebx .esi 0 0 0 ++ mulA ++ advance

/-- One block. -/
def body (b : Blocks) : Prog isa := .seq (.block pre) (.seq (blkCall b) (.block post))

def encrypt (b : Blocks) : Prog isa := whole (body b)

def decrypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesXts.X86
