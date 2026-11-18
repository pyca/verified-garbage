module

public import VerifiedGarbage.Impl.AesCbc.X86

/-!
# AES-CTR: x86 (32-bit) implementation

`vg_aes_ctr(schedule, rounds, ctr, data, n, scratch)` (see
`VG.Spec.Ctr.aesContract`), every argument on the stack (cdecl), composed
of calls of the verified `vg_aes_ctr32_to`, in place, on as many blocks as
it can take at once (`crypt32`), as on x86-64 (`Impl/AesCtr/X86_64.lean`).
It is generic over the implementation it calls (`Ctr32`): it is emitted
once for each implementation (e.g. `vg_aes_ctr_aesni` calls
`vg_aes_ctr32_to_aesni`).

It is built from AES-CMAC's pieces (`Impl/CmacAes/X86.lean`), whose
arguments are in the same places: `setup` saves our caller's `ebx`, `esi`,
`edi` and `ebp` in the scratch buffer and points `esi` at the first block,
and `restore 5` restores them. `esi` points at the next block across the
calls, and the other arguments are reloaded from the stack.

`vg_aes_ctr32_to` increments only the last 32 bits of the counter block. So,
as OpenSSL's `CRYPTO_ctr128_encrypt_ctr32` does, each call takes
`m = min(left, 2³² − c)` blocks, with `c` the last 32 bits of the counter
block (`count`): `m − 1` is the smaller of `left − 1` and `2³² − 1 − c`
(`c` with every bit flipped), selected by a mask made with `cmp` and `sbb`.
The call (`ctrCall`, which pushes the seven arguments in a frame of its own:
with the return address, the 32 bytes below `esp`) keeps `edi`, which holds
`m`, and `esi`; it leaves the counter block `m` further on in its last 32
bits, and if they wrapped around to 0, the first 96 bits are incremented
(`carry`: three words, loaded and byte-reversed with `bswap`, the last plus
1 and each other plus the carry out of the one after it, reversed again
and stored). `done` sets ZF once `esi` reaches `data + 16 n`.

`crypt` is the function this one replaced, which calls
`vg_aes_encrypt_blocks` on one block at a time: `vg_aes_ctr_final`
(`Impl/AesCtr/X86/Final.lean`) calls it, as an internal function, on its one
block. Each block, the counter block is copied to the scratch buffer (at
2048, where CBC's decryption keeps a block) and enciphered there, giving
the next output block, which is XORed into the data block; then the counter
block is incremented as a 128-bit big-endian number: its four words loaded,
byte-reversed (`bswap`), added to with `add` and `adc`, reversed again and
stored.

Only the pointers, `rounds`, `n` and, in `crypt32`, the last 32 bits of the
counter block can affect timing.
-/

@[expose] public section

namespace VG.Impl.AesCtr.X86

open VG.X86
open VG.Impl.Aes.X86 (Blocks)
open VG.Impl.Aes.X86 (Ctr32)
open VG.Impl.CmacAes.X86 (argOp at_ advance xor4 zero4 ctrCall)
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

/-! ## `vg_aes_ctr`, over `vg_aes_ctr32_to` -/

/-- The blocks of this call, `m = min(left, 2³² − c)`, in `edi`, with the
counter block's address in `edx`: `ecx` is `2³² − 1 − c`, `edi` is
`left − 1` (`n` less the blocks before `esi`, less 1), `eax` the mask of
`ecx < edi`, and `edi` becomes the smaller of the two, plus 1. -/
def count : List Instr :=
  [.mov .edx (argOp 2), .mov .ecx (.mem (at_ .edx 12)), .bswap .ecx, .alu .xor .ecx (.imm 0xFFFFFFFF),
   .mov .edi (argOp 4), .mov .eax (.reg .esi), .alu .sub .eax (argOp 3), .shift .shr .eax 4,
   .alu .sub .edi (.reg .eax), .alu .sub .edi (.imm 1),
   .alu .cmp .ecx (.reg .edi), .alu .sbb .eax (.reg .eax), .alu .xor .ecx (.reg .edi),
   .alu .and .ecx (.reg .eax), .alu .xor .edi (.reg .ecx), .alu .add .edi (.imm 1)]

/-- The other arguments of `vg_aes_ctr32_to`: the schedule and the rounds
(our stack arguments 0 and 1), the blocks at `esi`, and the working space
(our stack argument 5). -/
def args : List Instr :=
  [.mov .eax (argOp 0), .mov .ecx (argOp 1), .mov .ebx (.reg .esi), .mov .ebp (argOp 5)]

/-- On past the `edi` blocks of the call, and ZF set if the last 32 bits of
the counter block wrapped around to 0. -/
def adv : List Instr :=
  [.mov .eax (.reg .edi), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .esi (.reg .eax), .mov .edx (argOp 2),
   .mov .eax (.mem (at_ .edx 12)), .alu .test .eax (.reg .eax)]

/-- The first 96 bits of the counter block at `edx` plus 1, big-endian. -/
def carry : List Instr :=
  [.mov .eax (.mem (at_ .edx 8)), .bswap .eax, .alu .add .eax (.imm 1),
   .mov .ecx (.mem (at_ .edx 4)), .bswap .ecx, .alu .adc .ecx (.imm 0),
   .mov .ebx (.mem (at_ .edx 0)), .bswap .ebx, .alu .adc .ebx (.imm 0),
   .bswap .eax, .store (at_ .edx 8) .eax, .bswap .ecx, .store (at_ .edx 4) .ecx,
   .bswap .ebx, .store (at_ .edx 0) .ebx]

/-- ZF set once `esi` reaches `data + 16 n`. -/
def done : List Instr :=
  [.mov .eax (argOp 4), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax), .alu .add .eax (.reg .eax),
   .alu .add .eax (.reg .eax), .alu .add .eax (argOp 3), .alu .cmp .esi (.reg .eax)]

/-- One call: the blocks it takes, the call, on past them, the carry if the
counter wrapped around, and ZF set if no blocks are left. -/
def body32 (c : Ctr32) : Prog isa :=
  .seq (.block (count ++ args)) (.seq (ctrCall c) (.seq (.block adv)
    (.seq (.ite .e (.block carry) (.block [])) (.block done))))

def crypt32 (c : Ctr32) : Prog isa := whole (body32 c)

end VG.Impl.AesCtr.X86
