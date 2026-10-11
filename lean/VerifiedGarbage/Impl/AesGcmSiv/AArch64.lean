module

public import VerifiedGarbage.Impl.AesGcm.AArch64

/-!
# AES-GCM-SIV: AArch64 implementation

`vg_aes_gcm_siv_seal(schedule = x0, rounds = x1, nonce = x2, aad = x3, aad_len = x4, data = x5, len = x6, tag = x7, work = [sp])`
and `vg_aes_gcm_siv_open` with the same arguments (`Spec/GcmSiv/Contract.lean`),
with the working space `work` as a last argument, which a frame on the stack
allocates (`Impl.StackScratch.AArch64.withStackArgScratch`), composed of calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key` and
`vg_ghash`, and generic over their implementations as AES-GCM is
(`Impl.AesGcm.AArch64.Callees`).

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  by `vg_aes_expand_key`, for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: up to 64 blocks
  at a time are copied to `W + 480` with their bytes reversed before
  `vg_ghash` absorbs them (`chunk`). The last bytes of a string, padded
  with zeros, and the lengths block are put in the block at `W + 224` and
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
  computes the tag of the plaintext at `W + 224` and compares the two without
  a branch (`cmp`), then ANDs every byte of the data with `0 − ok` (`mask`).

## The working space `W` (3808 bytes)

* `[0, 16)`: the tag (the one `seal` computes, or the received one);
  `[16, 32)`: the authentication key; `[32, 64)`: the encryption key;
  `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator; `[96, 112)`: the
  counter block (or the tag input); `[112, 128)`: a copy of it for a call;
  `[128, 216)`: our caller's `x19`–`x28` and our return address `x30` (as
  AES-GCM saves them); `[216, 224)`: `tag`'s address; `[224, 240)`: a block
  (and the tag `open` computes);
* `[240, 480)`: the encryption key's schedule; `[480, 1504)`: the reversed
  blocks; `[1504, 1760)`: `vg_ghash`'s working space; `[1760, 3808)`:
  `vg_aes_ctr32`'s, and `vg_aes_expand_key`'s at its start.

## Registers

The arguments stay where the functions called preserve them: `x19` holds
`W`, `x20` the nonce, `x21` the key schedule, `x22` the number of rounds,
`x23` and `x24` the additional data and its length, `x25` and `x26` the data
and its length. The pieces take a pointer in `x27` and a number of bytes in
`x28`, which the callees also preserve.

The model has no flags or register-offset addressing: the branches are
`cbz`/`cbnz` on lengths and counts, and the bytes are copied, XORed and
masked through advancing pointers. Only the pointers, the lengths and
`rounds` affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.AArch64

open VG.AArch64
open VG.Impl.AesGcm.AArch64 (Callees mov ptr imm save restore copyLoop xorLoop)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cbO : Nat := 96
def ccO : Nat := 112
def tagPO : Nat := 216
def bO : Nat := 224
def skO : Nat := 240
def revO : Nat := 480
def ghO : Nat := 1504
def scrO : Nat := 1760

variable (c : Callees)

def callCtr : Prog isa := .call c.ctr.name c.ctr.code
def callKey : Prog isa := .call c.key.name c.key.code
def callGh : Prog isa := .call c.gh.name c.gh.code

/-- The 16 bytes at `W + s` copied to `W + d`. -/
def copy16 (s d : Nat) : List Instr :=
  [.ldr .x .x9 .x19 s, .str .x .x9 .x19 d, .ldr .x .x9 .x19 (s + 8), .str .x .x9 .x19 (d + 8)]

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [imm .x9 0, .str .x .x9 .x19 d, .str .x .x9 .x19 (d + 8)]

/-- The arguments of `vg_aes_ctr32` but the data: the encryption key's
schedule, the counter block's copy at `W + 112`, one block and the working
space. -/
def ctrArgs : List Instr := [ptr .x0 .x19 skO, mov .x1 .x22, ptr .x2 .x19 ccO, imm .x4 1, ptr .x5 .x19 scrO]

/-! ## The keys -/

/-- `little_endian_uint32(x27) ‖ nonce` at `W + 112`, a zero block at
`W + 224`, and the arguments of `vg_aes_ctr32` with the key-generating key's
schedule. -/
def deriveBlock : List Instr :=
  ([.ldr .w .x9 .x20 0, .ldr .w .x10 .x20 4, .ldr .w .x11 .x20 8, .str .w .x27 .x19 ccO,
    .str .w .x9 .x19 (ccO + 4), .str .w .x10 .x19 (ccO + 8), .str .w .x11 .x19 (ccO + 12)] : List Instr) ++ zero16 bO ++
    [mov .x0 .x21, mov .x1 .x22, ptr .x2 .x19 ccO, ptr .x3 .x19 bO, imm .x4 1, ptr .x5 .x19 scrO]

/-- The first 8 bytes of the block kept at `W + 16 + 8 x27`, the next `x27`,
and `x10` zero after the last block (`rounds / 2 - 1` of them). -/
def derivePost : List Instr :=
  [.ldr .x .x9 .x19 bO, .lsl .x .x10 .x27 3, .add .x .x10 .x19 .x10, .str .x .x9 .x10 akO,
    .addImm .x .x27 .x27 1, .lsr .x .x10 .x22 1, .subImm .x .x10 .x10 1, .sub .x .x10 .x10 .x27]

/-- The message keys, 8 bytes per block, from `W + 16`. -/
def derive : Prog isa :=
  .seq (.block [imm .x27 0])
    (.loop (.seq (.block deriveBlock) (.seq (callCtr c) (.block derivePost))) (.nonzero .x .x10))

/-- The arguments of `vg_aes_expand_key`: the encryption key, whose length
is `4 (rounds − 6)`, its schedule at `W + 240` and the working space. -/
def expandArgs : List Instr :=
  [ptr .x0 .x19 ekO, .subImm .x .x1 .x22 6, .lsl .x .x1 .x1 2, ptr .x2 .x19 skO, ptr .x3 .x19 scrO]

/-- The encryption key's schedule at `W + 240`. -/
def expand : Prog isa := .seq (.block expandArgs) (callKey c)

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number), in GHASH's order at `W + 64`, and its accumulator zeroed. -/
def hkey : List Instr :=
  ([.ldr .x .x9 .x19 akO, .ldr .x .x10 .x19 (akO + 8), imm .x11 1, .logic .and .x .x12 .x9 .x11,
    imm .x13 0, .sub .x .x12 .x13 .x12, .lsr .x .x9 .x9 1, .logic .and .x .x13 .x10 .x11,
    .ror .x .x13 .x13 1, .logic .orr .x .x9 .x9 .x13, .lsr .x .x10 .x10 1, .movz .x .x11 0xE100 3,
    .logic .and .x .x11 .x11 .x12, .logic .eor .x .x10 .x10 .x11, .rev .x10 .x10, .rev .x9 .x9,
    .str .x .x10 .x19 hO, .str .x .x9 .x19 (hO + 8)] : List Instr) ++ zero16 yO

/-- The keys and GHASH's key. -/
def keys : Prog isa := .seq (derive c) (.seq (expand c) (.block hkey))

/-! ## POLYVAL -/

/-- `vg_ghash`'s arguments but the blocks and their number. -/
def ghArgs : List Instr := [ptr .x0 .x19 hO, ptr .x1 .x19 yO, ptr .x4 .x19 ghO]

/-- `x10 := min (x28 / 16, 64)`. -/
def chunkLen : Prog isa :=
  .seq (.block [.lsr .x .x10 .x28 10])
    (.ite (.zero .x .x10) (.block [.lsr .x .x10 .x28 4]) (.block [imm .x10 64]))

/-- The `x15` (at least 1) blocks at `x11` copied to `x14`, the bytes of
each reversed. -/
def revLoop : Prog isa :=
  .loop (.block [.ldr .x .x12 .x11 0, .ldr .x .x13 .x11 8, .rev .x12 .x12, .rev .x13 .x13,
    .str .x .x13 .x14 0, .str .x .x12 .x14 8, ptr .x11 .x11 16, ptr .x14 .x14 16,
    .subImm .x .x15 .x15 1]) (.nonzero .x .x15)

/-- After the copies: `x27` and `x28` past the blocks, and the arguments of
`vg_ghash`. -/
def chunkArgs : List Instr :=
  ([.lsl .x .x9 .x10 4, .add .x .x27 .x27 .x9, .sub .x .x28 .x28 .x9] : List Instr) ++ ghArgs ++
    [ptr .x2 .x19 revO, mov .x3 .x10]

/-- Up to 64 of the whole blocks of the `x28` bytes at `x27` reversed at
`W + 480`, `x27` and `x28` past them, and the arguments of `vg_ghash`. -/
def chunkPre : Prog isa :=
  .seq chunkLen
  (.seq (.block [mov .x11 .x27, ptr .x14 .x19 revO, mov .x15 .x10])
  (.seq revLoop (.block chunkArgs)))

/-- Up to 64 of the whole blocks of the `x28` bytes at `x27`, reversed and
absorbed; `x27` and `x28` past them, and `x9` their number of whole blocks
left. -/
def chunk : Prog isa := .seq chunkPre (.seq (callGh c) (.block [.lsr .x .x9 .x28 4]))

/-- The last `x28` (1 to 15) bytes at `x27`, padded with zeros at `W + 224`,
as the 16 bytes to absorb. -/
def absTailPre : Prog isa :=
  .seq (.block (zero16 bO ++ [ptr .x11 .x19 bO, mov .x12 .x27, mov .x13 .x28]))
  (.seq copyLoop (.block [ptr .x27 .x19 bO, imm .x28 16]))

/-- The last `x28` (1 to 15) bytes at `x27`, padded with zeros at `W + 224`,
absorbed. -/
def absTail : Prog isa := .seq absTailPre (chunk c)

/-- The `x28` bytes at `x27`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block [.lsr .x .x9 .x28 4])
  (.seq (.ite (.zero .x .x9) (.block []) (.loop (chunk c) (.nonzero .x .x9)))
    (.ite (.zero .x .x28) (.block []) (absTail c)))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, at `W + 224`, as
the bytes to absorb. -/
def lensBlock : List Instr :=
  [.lsl .x .x9 .x24 3, .str .x .x9 .x19 bO, .lsl .x .x9 .x26 3, .str .x .x9 .x19 (bO + 8),
    ptr .x27 .x19 bO, imm .x28 16]

/-- The lengths block absorbed. -/
def lens : Prog isa := .seq (.block lensBlock) (chunk c)

/-- The tag input at `W + 96`: POLYVAL's result in its own order, its first
12 bytes XORed with the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.ldr .x .x9 .x19 (yO + 8), .rev .x9 .x9, .ldr .x .x10 .x19 yO, .rev .x10 .x10,
    .ldr .x .x11 .x20 0, .logic .eor .x .x9 .x9 .x11, .ldr .w .x11 .x20 8,
    .logic .eor .x .x10 .x10 .x11, .lsl .x .x10 .x10 1, .lsr .x .x10 .x10 1,
    .str .x .x9 .x19 cbO, .str .x .x10 .x19 (cbO + 8)]

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block [mov .x27 .x23, mov .x28 .x24])
  (.seq (absorb c)
  (.seq (.block [mov .x27 .x25, mov .x28 .x26])
  (.seq (absorb c)
  (.seq (lens c) (.block tagIn)))))

/-- The encryption of the block at `W + 96` with the encryption key, at
`W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ [ptr .x3 .x19 o])) (callCtr c)

/-! ## Counter mode -/

/-- The counter block from the tag at `W`, with the top bit of its last
byte set, and the data as the bytes to encrypt. -/
def cryptHead : List Instr :=
  [.ldr .x .x9 .x19 tagO, .str .x .x9 .x19 cbO, .ldr .x .x9 .x19 (tagO + 8), .movz .x .x10 0x8000 3,
    .logic .orr .x .x9 .x9 .x10, .str .x .x9 .x19 (cbO + 8), mov .x27 .x25, mov .x28 .x26,
    .lsr .x .x9 .x28 4]

/-- One block at `x27` encrypted in place from the counter block, which is
then incremented; `x27` and `x28` past it, and `x9` the whole blocks left. -/
def cryptBlock : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ ctrArgs ++ [mov .x3 .x27]))
  (.seq (callCtr c)
    (.block [.ldr .w .x9 .x19 cbO, .addImm .w .x9 .x9 1, .str .w .x9 .x19 cbO, ptr .x27 .x27 16,
      .subImm .x .x28 .x28 16, .lsr .x .x9 .x28 4]))

/-- The last `x28` (1 to 15) bytes at `x27` XORed with a keystream block,
computed at `W + 224`. -/
def cryptTail : Prog isa :=
  .seq (tag c bO) (.seq (.block [ptr .x11 .x19 bO, mov .x12 .x27, mov .x13 .x28]) xorLoop)

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (.ite (.zero .x .x9) (.block []) (.loop (cryptBlock c) (.nonzero .x .x9)))
    (.ite (.zero .x .x28) (.block []) (cryptTail c)))

/-! ## Comparing tags and masking -/

/-- `x27 = 1` if the tags at `W` and `W + 224` are equal, 0 if not, without
a branch: the carry of adding all ones to their difference is 0 only when it
is zero. -/
def cmp : List Instr :=
  [.ldr .x .x9 .x19 tagO, .ldr .x .x10 .x19 bO, .logic .eor .x .x9 .x9 .x10,
    .ldr .x .x10 .x19 (tagO + 8), .ldr .x .x11 .x19 (bO + 8), .logic .eor .x .x10 .x10 .x11,
    .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1, .adds .x .x9 .x9 .x12,
    .adcs .x .x10 .x11 .x11, imm .x27 1, .sub .x .x27 .x27 .x10]

/-- Every byte of the data ANDed with `0 − x27`. -/
def mask : Prog isa :=
  .seq (.block [imm .x9 0, .sub .x .x11 .x9 .x27, mov .x12 .x25, mov .x13 .x26])
    (.ite (.zero .x .x13) (.block [])
      (.loop (.block [.ldrb .x14 .x12 0, .logic .and .w .x14 .x14 .x11, .strb .x14 .x12 0,
        ptr .x12 .x12 1, .subImm .x .x13 .x13 1]) (.nonzero .x .x13)))

/-! ## The functions -/

/-- `(schedule = x0, rounds = x1, nonce = x2, aad = x3, aad_len = x4, data = x5,
len = x6, tag = x7, work = [sp])`: our caller's registers saved in `W`, the
arguments kept in `x19`–`x26`, and `tag` at `W + 216`. -/
def entry : List Instr :=
  ([.ldrSp .x9 0] : List Instr) ++ save .x9 ++ [mov .x19 .x9, mov .x20 .x2, mov .x21 .x0, mov .x22 .x1, mov .x23 .x3,
    mov .x24 .x4, mov .x25 .x5, mov .x26 .x6, .str .x .x7 .x19 tagPO]

/-- The received tag copied from `tag` to `W`. -/
def recv : List Instr :=
  [.ldr .x .x9 .x19 tagPO, .ldr .x .x10 .x9 0, .str .x .x10 .x19 tagO, .ldr .x .x10 .x9 8,
    .str .x .x10 .x19 (tagO + 8)]

/-- The tag copied from `W` to `tag`. -/
def tagOut : List Instr :=
  [.ldr .x .x9 .x19 tagPO, .ldr .x .x10 .x19 tagO, .str .x .x10 .x9 0, .ldr .x .x10 .x19 (tagO + 8),
    .str .x .x10 .x9 8]

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq (keys c) (.seq (polyval c) (.seq (tag c tagO) (.seq (crypt c)
    (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq (keys c) (.seq (crypt c) (.seq (polyval c) (.seq (tag c bO)
    (.seq (.block cmp) (.seq mask (.block ([mov .x0 .x27] ++ restore)))))))))

end VG.Impl.AesGcmSiv.AArch64
