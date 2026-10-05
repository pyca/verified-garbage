import VerifiedGarbage.Impl.AesGcm.Arm

/-!
# AES-GCM-SIV: 32-bit ARM implementation

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Spec/GcmSiv/Contract.lean`),
with the working space `work` as a last argument, which a frame on the
stack allocates (`Impl.StackScratch.Arm.withStackScratch`), composed of
calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key` and `vg_ghash`, as
on AArch64 (`Impl/AesGcmSiv/AArch64.lean`):

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  by `vg_aes_expand_key`, for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: up to 64 blocks
  at a time are copied to `W + 432` with their bytes reversed before
  `vg_ghash` absorbs them (`chunk`). The last bytes of a string, padded
  with zeros, and the lengths block are put in the block at `W + 176` and
  absorbed the same way (`absorb`, `lens`); the result is read back
  reversed (`tagIn`).
* The tag is `vg_aes_ctr32` of the tag input on a zero block (`tag`).
* Counter mode (§4) increments the first 4 bytes of the counter block, as a
  little-endian number, which `vg_aes_ctr32` (which increments the last 4,
  big-endian) does not: each block is encrypted by a call of its own from a
  copy of the counter block, which is then incremented (`cryptBlock`); the
  last bytes are XORed with a keystream block computed as a tag is
  (`cryptTail`).
* `seal` copies the tag from `W` to `tag` at the end (`tagOut`); `open`
  copies the received tag from `tag` to `W` first (`recv`), decrypts,
  computes the tag of the plaintext at `W + 176` and compares the two without
  a branch (`cmp`), then ANDs every byte of the data with `0 − ok` (`mask`).

`vg_aes_ctr32` and `vg_ghash` take arguments on the stack, which frames push
around their calls (`Impl.AesGcm.Arm.ctrFrame`, `ghFrame`): the functions
use 8 bytes of stack below the frame holding `W`.

## The working space `W` (3760 bytes)

* `[0, 16)`: the tag (the one `seal` computes, or the received one);
  `[16, 32)`: the authentication key; `[32, 64)`: the encryption key;
  `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator; `[96, 112)`: the
  counter block (or the tag input); `[112, 128)`: a copy of it for a call;
  `[128, 164)`: our caller's `r4`–`r11` and our return address `lr` (as
  AES-GCM saves them); `[164, 176)`: unused, so that the parts after it start
  at multiples of 16, as an `add` immediate past 1020 must; `[176, 192)`: a
  block (and the tag `open` computes);
* `[192, 432)`: the encryption key's schedule; `[432, 1456)`: the reversed
  blocks; `[1456, 1712)`: `vg_ghash`'s working space; `[1712, 3760)`:
  `vg_aes_ctr32`'s, and `vg_aes_expand_key`'s at its start.

## Registers and arguments

`(schedule = r0, rounds = r1, nonce = r2, aad = r3, aad_len = [sp],
data = [sp + 4], len = [sp + 8], tag = [sp + 12], work = [sp + 16])`. The
arguments in registers stay where the functions called preserve them: `r11`
holds `W`, `r10` the nonce, `r9` the key schedule, `r8` the number of rounds
and `r7` the additional data; the stack arguments are read when they are needed
(the stack pointer is the one on entry outside the frames). The pieces take
a pointer in `r4` and a number of bytes in `r5`, which the callees also
preserve, and `chunk` its number of blocks in `r6`. `r0`–`r3`, `r12` and
`lr` are temporaries.

The model has no register-offset addressing and branches only on `Z`: the
bytes are copied, XORed and masked through advancing pointers, counting
down with `subs`. Only the pointers, the lengths and `rounds` affect timing.
-/

namespace VG.Impl.AesGcmSiv.Arm

open VG.Arm
open VG.Impl.AesGcm.Arm (imm addI save restore ctrFrame ghFrame copyLoop xorLoop zero16)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cbO : Nat := 96
def ccO : Nat := 112
def bO : Nat := 176
def skO : Nat := 192
def revO : Nat := 432
def ghO : Nat := 1456
def scrO : Nat := 1712

/-- The 16 bytes at `W + s` copied to `W + d` (all loads first). -/
def copy16 (s d : Nat) : List Instr :=
  [.ldr .r0 .r11 s, .ldr .r1 .r11 (s + 4), .ldr .r2 .r11 (s + 8), .ldr .r3 .r11 (s + 12), .str .r0 .r11 d,
   .str .r1 .r11 (d + 4), .str .r2 .r11 (d + 8), .str .r3 .r11 (d + 12)]

/-- The arguments of `vg_aes_ctr32` but the data: the encryption key's
schedule, the counter block's copy at `W + 112`, one block and the working
space. -/
def ctrArgs : List Instr :=
  [addI .r0 .r11 skO, .mov .r1 (.reg .r8), addI .r2 .r11 ccO, .mov .r12 (imm 1), addI .lr .r11 scrO]

/-! ## The keys -/

/-- `little_endian_uint32(r4) ‖ nonce` at `W + 112`, a zero block at
`W + 176`, and the arguments of `vg_aes_ctr32` with the key-generating key's
schedule. -/
def deriveBlock : List Instr :=
  [.ldr .r0 .r10 0, .ldr .r1 .r10 4, .ldr .r2 .r10 8, .str .r4 .r11 ccO, .str .r0 .r11 (ccO + 4),
    .str .r1 .r11 (ccO + 8), .str .r2 .r11 (ccO + 12)] ++ zero16 bO ++
    [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r11 ccO, addI .r3 .r11 bO, .mov .r12 (imm 1),
     addI .lr .r11 scrO]

/-- The first 8 bytes of the block kept at `W + 16 + 8 r4`, the next `r4`,
and `Z` set after the last block (`rounds / 2 - 1` of them). -/
def derivePost : List Instr :=
  [.ldr .r0 .r11 bO, .ldr .r1 .r11 (bO + 4), .dp .add .r2 .r11 (.shifted .r4 .lsl 3), .str .r0 .r2 akO,
    .str .r1 .r2 (akO + 4), addI .r4 .r4 1, .mov .r12 (.shifted .r8 .lsr 1), .dp .sub .r12 .r12 (imm 1),
    .subs .r12 .r12 (.reg .r4)]

/-- The message keys, 8 bytes per block, from `W + 16`. -/
def derive : Prog isa :=
  .seq (.block [.mov .r4 (imm 0)]) (.loop (.seq (.block deriveBlock) (.seq ctrFrame (.block derivePost))) .ne)

/-- The arguments of `vg_aes_expand_key`: the encryption key, whose length
is `4 (rounds − 6)`, its schedule at `W + 192` and the working space. -/
def expandArgs : List Instr :=
  [addI .r0 .r11 ekO, .dp .sub .r1 .r8 (imm 6), .mov .r1 (.shifted .r1 .lsl 2), addI .r2 .r11 skO,
   addI .r3 .r11 scrO]

/-- The encryption key's schedule at `W + 192`. -/
def expand : Prog isa := .seq (.block expandArgs) (.call "vg_aes_expand_key_scratch" Impl.Aes.Arm.expandKey)

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number, in the words `r0`–`r3`), in GHASH's order at `W + 64`, and its
accumulator zeroed. -/
def hkey : List Instr :=
  [.ldr .r0 .r11 akO, .ldr .r1 .r11 (akO + 4), .ldr .r2 .r11 (akO + 8), .ldr .r3 .r11 (akO + 12),
    .dp .and .r12 .r0 (imm 1), .mov .lr (imm 0), .dp .sub .r12 .lr (.reg .r12),
    .mov .r0 (.shifted .r0 .lsr 1), .dp .orr .r0 .r0 (.shifted .r1 .lsl 31),
    .mov .r1 (.shifted .r1 .lsr 1), .dp .orr .r1 .r1 (.shifted .r2 .lsl 31),
    .mov .r2 (.shifted .r2 .lsr 1), .dp .orr .r2 .r2 (.shifted .r3 .lsl 31),
    .mov .r3 (.shifted .r3 .lsr 1), .dp .and .r12 .r12 (imm 0xE1000000), .dp .eor .r3 .r3 (.reg .r12),
    .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
    .str .r3 .r11 hO, .str .r2 .r11 (hO + 4), .str .r1 .r11 (hO + 8), .str .r0 .r11 (hO + 12)] ++ zero16 yO

/-- The keys and GHASH's key. -/
def keys : Prog isa := .seq derive (.seq expand (.block hkey))

/-! ## POLYVAL -/

/-- `r6 := min (r5 / 16, 64)`. -/
def chunkLen : Prog isa :=
  .seq (.block [.mov .r6 (.shifted .r5 .lsr 10), .cmp .r6 (imm 0)])
    (.ite .eq (.block [.mov .r6 (.shifted .r5 .lsr 4)]) (.block [.mov .r6 (imm 64)]))

/-- The `r3` (at least 1) blocks at `r4` copied to `r2`, the bytes of each
reversed, advancing both. -/
def revLoop : Prog isa :=
  .loop (.block [.ldr .r0 .r4 12, .ldr .r1 .r4 8, .ldr .r12 .r4 4, .ldr .lr .r4 0, .rev .r0 .r0, .rev .r1 .r1,
    .rev .r12 .r12, .rev .lr .lr, .str .r0 .r2 0, .str .r1 .r2 4, .str .r12 .r2 8, .str .lr .r2 12,
    addI .r4 .r4 16, addI .r2 .r2 16, .subs .r3 .r3 (imm 1)]) .ne

/-- After the copies: `r5` past the blocks, and the arguments of `vg_ghash`. -/
def chunkArgs : List Instr :=
  [.dp .sub .r5 .r5 (.shifted .r6 .lsl 4), addI .r0 .r11 hO, addI .r1 .r11 yO, addI .r2 .r11 revO,
   .mov .r3 (.reg .r6), addI .r12 .r11 ghO]

/-- Up to 64 of the whole blocks of the `r5` bytes at `r4` reversed at
`W + 432`, `r4` and `r5` past them, and the arguments of `vg_ghash`. -/
def chunkPre : Prog isa :=
  .seq chunkLen
  (.seq (.block [addI .r2 .r11 revO, .mov .r3 (.reg .r6)])
  (.seq revLoop (.block chunkArgs)))

/-- `Z` set iff fewer than 16 of the `r5` bytes are left. -/
def wholeLeft : List Instr := [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)]

/-- Up to 64 of the whole blocks of the `r5` bytes at `r4`, reversed and
absorbed; `r4` and `r5` past them, and `Z` set if no whole block is left. -/
def chunk : Prog isa := .seq chunkPre (.seq ghFrame (.block wholeLeft))

/-- The last `r5` (1 to 15) bytes at `r4`, padded with zeros at `W + 176`,
as the 16 bytes to absorb. -/
def absTailPre : Prog isa :=
  .seq (.block (zero16 bO ++ [.mov .r1 (.reg .r4), addI .r2 .r11 bO, .mov .r3 (.reg .r5)]))
  (.seq copyLoop (.block [addI .r4 .r11 bO, .mov .r5 (imm 16)]))

/-- The last `r5` (1 to 15) bytes at `r4`, padded with zeros at `W + 176`,
absorbed. -/
def absTail : Prog isa := .seq absTailPre chunk

/-- The `r5` bytes at `r4`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block wholeLeft)
  (.seq (.ite .eq (.block []) (.loop chunk .ne))
  (.seq (.block [.cmp .r5 (imm 0)]) (.ite .eq (.block []) absTail)))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, at `W + 176`, as
the bytes to absorb. -/
def lensBlock : List Instr :=
  [.ldrSp .r0 0, .ldrSp .r2 8, .mov .r1 (.shifted .r0 .lsl 3), .str .r1 .r11 bO, .mov .r1 (.shifted .r0 .lsr 29),
   .str .r1 .r11 (bO + 4), .mov .r1 (.shifted .r2 .lsl 3), .str .r1 .r11 (bO + 8),
   .mov .r1 (.shifted .r2 .lsr 29), .str .r1 .r11 (bO + 12), addI .r4 .r11 bO, .mov .r5 (imm 16)]

/-- The lengths block absorbed. -/
def lens : Prog isa := .seq (.block lensBlock) chunk

/-- The tag input at `W + 96`: POLYVAL's result in its own order (the words
of the accumulator in the other order, each reversed), its first 12 bytes
XORed with the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.ldr .r0 .r11 (yO + 12), .ldr .r1 .r11 (yO + 8), .ldr .r2 .r11 (yO + 4), .ldr .r3 .r11 yO, .rev .r0 .r0,
   .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3, .ldr .r12 .r10 0, .dp .eor .r0 .r0 (.reg .r12), .ldr .r12 .r10 4,
   .dp .eor .r1 .r1 (.reg .r12), .ldr .r12 .r10 8, .dp .eor .r2 .r2 (.reg .r12), .mov .r3 (.shifted .r3 .lsl 1),
   .mov .r3 (.shifted .r3 .lsr 1), .str .r0 .r11 cbO, .str .r1 .r11 (cbO + 4), .str .r2 .r11 (cbO + 8),
   .str .r3 .r11 (cbO + 12)]

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block [.mov .r4 (.reg .r7), .ldrSp .r5 0])
  (.seq absorb
  (.seq (.block [.ldrSp .r4 4, .ldrSp .r5 8])
  (.seq absorb
  (.seq lens (.block tagIn)))))

/-- The encryption of the block at `W + 96` with the encryption key, at
`W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [addI .r3 .r11 o])) ctrFrame

/-! ## Counter mode -/

/-- The counter block from the tag at `W`, with the top bit of its last
byte set, and the data as the bytes to encrypt; `Z` set if it has no whole
block. -/
def cryptHead : List Instr :=
  [.ldrSp .r4 4, .ldrSp .r5 8, .ldr .r0 .r11 tagO, .ldr .r1 .r11 (tagO + 4), .ldr .r2 .r11 (tagO + 8),
   .ldr .r3 .r11 (tagO + 12), .dp .orr .r3 .r3 (imm 0x80000000), .str .r0 .r11 cbO, .str .r1 .r11 (cbO + 4),
   .str .r2 .r11 (cbO + 8), .str .r3 .r11 (cbO + 12)] ++ wholeLeft

/-- After a block: the counter block's first word incremented, `r4` and `r5`
past the block, and `Z` set if no whole block is left. -/
def blockNext : List Instr :=
  [.ldr .r0 .r11 cbO, addI .r0 .r0 1, .str .r0 .r11 cbO, addI .r4 .r4 16, .dp .sub .r5 .r5 (imm 16)] ++ wholeLeft

/-- One block at `r4` encrypted in place from the counter block, which is
then incremented; `r4` and `r5` past it, and `Z` set if no whole block is
left. -/
def cryptBlock : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ ctrArgs ++ ([.mov .r3 (.reg .r4)] : List Instr))) (.seq ctrFrame (.block blockNext))

/-- The last `r5` (1 to 15) bytes at `r4` XORed with a keystream block,
computed at `W + 176`. -/
def cryptTail : Prog isa :=
  .seq (tag bO) (.seq (.block [addI .r1 .r11 bO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop)

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (.ite .eq (.block []) (.loop cryptBlock .ne))
  (.seq (.block [.cmp .r5 (imm 0)]) (.ite .eq (.block []) cryptTail)))

/-! ## Comparing tags and masking -/

/-- Word `k` of the XOR of the two tags into `d`. -/
def xorW (d : Reg) (k : Nat) : List Instr :=
  [.ldr d .r11 (tagO + 4 * k), .ldr .r2 .r11 (bO + 4 * k), .dp .eor d d (.reg .r2)]

/-- `r0 = 1` if the tags at `W` and `W + 176` are equal, 0 if not, without a
branch (`1 - ((x | -x) >> 31)` of the OR `x` of the XORs of their words). -/
def cmp : List Instr :=
  xorW .r0 0 ++ xorW .r1 1 ++ [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 2 ++
    [.dp .orr .r0 .r0 (.reg .r1)] ++ xorW .r1 3 ++
    [.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
     .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
     .dp .sub .r0 .r1 (.reg .r0)]

/-- Every byte of the data ANDed with `0 − r0`. -/
def mask : Prog isa :=
  .seq (.block [.ldrSp .r4 4, .ldrSp .r5 8, .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1,
        .subs .r5 .r5 (imm 1)]) .ne))

/-! ## The functions -/

/-- Our caller's registers saved in `W`, and the arguments kept in
`r7`–`r11`. -/
def entry : List Instr :=
  .ldrSp .r12 16 :: save .r12 ++
    [.mov .r11 (.reg .r12), .mov .r10 (.reg .r2), .mov .r9 (.reg .r0), .mov .r8 (.reg .r1), .mov .r7 (.reg .r3)]

/-- The received tag copied from `tag`, at `[sp + 12]`, to `W`. -/
def recv : List Instr :=
  [.ldrSp .r1 12, .ldr .r0 .r1 0, .ldr .r2 .r1 4, .ldr .r3 .r1 8, .ldr .r12 .r1 12, .str .r0 .r11 tagO,
   .str .r2 .r11 (tagO + 4), .str .r3 .r11 (tagO + 8), .str .r12 .r11 (tagO + 12)]

/-- The tag copied from `W` to `tag`, at `[sp + 12]`. -/
def tagOut : List Instr :=
  [.ldrSp .r1 12, .ldr .r0 .r11 tagO, .ldr .r2 .r11 (tagO + 4), .ldr .r3 .r11 (tagO + 8),
   .ldr .r12 .r11 (tagO + 12), .str .r0 .r1 0, .str .r2 .r1 4, .str .r3 .r1 8, .str .r12 .r1 12]

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq keys (.seq polyval (.seq (tag tagO) (.seq crypt (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq keys (.seq crypt (.seq polyval (.seq (tag bO)
    (.seq (.block cmp) (.seq mask (.block restore))))))))

end VG.Impl.AesGcmSiv.Arm
