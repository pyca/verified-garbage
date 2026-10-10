import VerifiedGarbage.Impl.AesCbc.X86

/-!
# AES-CTR: x86 (32-bit) implementation

`vg_aes_ctr(schedule, rounds, ctr, data, n, scratch)` (see
`VG.Spec.Ctr.aesContract`), every argument on the stack (cdecl), composed
of calls of the verified `vg_aes_encrypt_blocks` on one block at a time. It
is generic over the implementation it calls (`Blocks`): it is emitted once
for each implementation (e.g. `vg_aes_ctr_aesni` calls
`vg_aes_encrypt_blocks_aesni`).

It is built from AES-CBC's pieces (`Impl/AesCbc/X86.lean`), whose arguments
are in the same places: `esi` points at the next block, and the other
arguments are reloaded from the stack. Each block, the counter block is
copied to the scratch buffer (at 2048, where CBC's decryption keeps a block)
and enciphered there, giving the next output block, which is XORed into the
data block; then the counter block is incremented as a 128-bit big-endian
number: its four words loaded, byte-reversed (`bswap`), added to with `add`
and `adc`, reversed again and stored.

Only the pointers, `rounds` and `n` can affect timing: the only branches are
on `n`.
-/

namespace VG.Impl.AesCtr.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4 zero4)
open VG.Impl.AesCbc.X86 (cOff whole blkCall)

/-- The counter block copied to `ebp + cOff`, and the arguments of the block
function: the schedule and the rounds (our stack arguments 0 and 1), the
copy, `n = 1`, and the working space (our stack argument 5). -/
def pre : List Instr :=
  ([.mov .ebp (argOp 5), .mov .ebx (argOp 2)] : List Instr) ++ zero4 .ebp cOff ++ xor4 .ebp .ebx .ebp cOff 0 cOff ++
  ([.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .ebp), .alu .add .ebx (.imm 2048),
   .mov .edi (.imm 1)] : List Instr)

/-- The counter block at `ebx` plus 1, modulo `2¹²⁸`, big-endian. -/
def incr : List Instr :=
  [.mov .eax (.mem (at_ .ebx 12)), .bswap .eax, .alu .add .eax (.imm 1),
   .mov .ecx (.mem (at_ .ebx 8)), .bswap .ecx, .alu .adc .ecx (.imm 0),
   .mov .edx (.mem (at_ .ebx 4)), .bswap .edx, .alu .adc .edx (.imm 0),
   .mov .edi (.mem (at_ .ebx 0)), .bswap .edi, .alu .adc .edi (.imm 0),
   .bswap .eax, .store (at_ .ebx 12) .eax, .bswap .ecx, .store (at_ .ebx 8) .ecx,
   .bswap .edx, .store (at_ .ebx 4) .edx, .bswap .edi, .store (at_ .ebx 0) .edi]

/-- The output block XORed into the data block, the counter block
incremented, and on to the next block. -/
def post : List Instr :=
  ([.mov .ebp (argOp 5)] : List Instr) ++ xor4 .esi .ebp .esi 0 cOff 0 ++ ([.mov .ebx (argOp 2)] : List Instr) ++ incr ++ advance

/-- One block. -/
def body (b : Blocks) : Prog isa := .seq (.block pre) (.seq (blkCall b) (.block post))

def crypt (b : Blocks) : Prog isa := whole (body b)

end VG.Impl.AesCtr.X86
