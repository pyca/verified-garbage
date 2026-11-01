module

public import VerifiedGarbage.Impl.AesGcm.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# AES-GCM-SIV: RISC-V implementation

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Spec/GcmSiv/Contract.lean`),
with the working space `work` as a last argument, which a frame on the
stack allocates (`Impl.StackScratch.RISCV64.withStackScratchArgs`), composed
of calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`, as on PPC64LE (`Impl/AesGcmSiv/PPC64LE.lean`), piece for piece:

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: up to 64 blocks
  at a time are copied to `W + 496` with their bytes reversed (each half
  loaded big-endian a byte at a time, `loadBE64`) before `vg_ghash` absorbs
  them (`chunk`). The last bytes of a string, padded with zeros, and the
  lengths block are put in the block at `W + 240` and absorbed the same way
  (`absorb`, `lens`); the result is read back reversed (`tagIn`).
* The tag is `vg_aes_ctr32` of the tag input on a zero block (`tag`).
* Counter mode (§4) increments the first 4 bytes of the counter block, as a
  little-endian number, which `vg_aes_ctr32` (which increments the last 4,
  big-endian) does not: each block is encrypted by a call of its own from a
  copy of the counter block, which is then incremented (`cryptBlock`); the
  last bytes are XORed with a keystream block computed as a tag is
  (`cryptTail`).
* `seal` copies the tag from `W` to `tag` at the end (`tagOut`); `open`
  copies the received tag from `tag` to `W` first (`recv`), decrypts,
  computes the tag of the plaintext at `W + 240` and compares the two
  without a branch (`cmp`), then ANDs every byte of the data with `0 − ok`
  (`mask`).

A call stores nothing in memory; `vg_ghash` uses 2048 bytes of stack below
the stack pointer for its table, the other callees none.

## The working space `W` (3840 bytes)

As on PPC64LE, with a copy of the nonce after the reversed blocks (every
offset below 2048, as loads, stores and `addi` encode them):

* `[0, 16)`: the tag (the one `seal` computes, or the received one);
  `[16, 32)`: the authentication key; `[32, 64)`: the encryption key;
  `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator; `[96, 112)`: the
  counter block (or the tag input); `[112, 128)`: a copy of it for a call;
  `[128, 224)`: our caller's `s0`–`s11`, and `[224, 232)` our return
  address (AES-GCM's `save`); `[240, 256)`: a block (and the tag `open`
  computes);
* `[256, 496)`: the encryption key's schedule; `[496, 1520)`: the reversed
  blocks; `[1520, 1532)`: the nonce; `[1536, 1792)`: `vg_ghash`'s working
  space; `[1792, 3840)`: `vg_aes_ctr32`'s, and
  `vg_aes_expand_key_scratch`'s at its start.

## Registers

`(schedule = a0, rounds = a1, nonce = a2, aad = a3, aad_len = a4, data = a5,
len = a6, tag = a7, work = [sp])`. The entry keeps `W` in `s0` and the
arguments in `s1`–`s8` (`nonce`, `schedule`, `rounds`, `aad`, `aad_len`,
`data`, `len`, `tag`), which the functions called preserve. The pieces take
a pointer in `s9` and a number of bytes in `s10`, which the callees also
preserve, and `derive` and `chunk` a count in `s11`; `open` keeps the result
of the comparison there. `a0`–`a7` and `t0`–`t6` are temporaries.

The model has no indexed byte access, and loads and stores fault unless
naturally aligned: the caller's buffers (the nonce, the additional data, the
data and the tag) are read and written a byte at a time, the nonce and the
tags copied to and from `W` on entry and exit, which the other pieces read a
doubleword at a time. Only the pointers, the lengths and `rounds` affect
timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.RISCV64

open VG.RISCV64
open VG.Impl.AesGcm.RISCV64 (mov ctrCall ghCall keyCall copyLoop xorLoop save restore)
open VG.Impl.Words.RISCV64 (loadBE64 storeBE copyBytes)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cbO : Nat := 96
def ccO : Nat := 112
def bO : Nat := 240
def skO : Nat := 256
def revO : Nat := 496
def ghO : Nat := 1536
def scrO : Nat := 1792
def nO : Nat := 1520

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [.li .t0 0, .store .d .t0 .s0 d, .store .d .t0 .s0 (d + 8)]

/-- The 16 bytes at `W + s` copied to `W + d`. -/
def copy16 (s d : Nat) : List Instr :=
  [.load .d .a0 .s0 s, .load .d .a1 .s0 (s + 8), .store .d .a0 .s0 d, .store .d .a1 .s0 (d + 8)]

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the encryption key's schedule, the counter block's copy at `W + 112` and the
working space. -/
def ctrArgs : List Instr := [.addi .a0 .s0 skO, mov .a1 .s3, .addi .a2 .s0 ccO, .addi .a5 .s0 scrO]

/-! ## The keys -/

/-- `little_endian_uint32(s11) ‖ nonce` at `W + 112`, a zero block at
`W + 240`, and the arguments of `vg_aes_ctr32` with the key-generating key's
schedule. -/
def deriveBlock : List Instr :=
  ([.load .w .a0 .s0 nO, .load .w .a1 .s0 (nO + 4), .load .w .a2 .s0 (nO + 8), .store .w .s11 .s0 ccO,
    .store .w .a0 .s0 (ccO + 4), .store .w .a1 .s0 (ccO + 8), .store .w .a2 .s0 (ccO + 12)] : List Instr) ++
    zero16 bO ++
    ([mov .a0 .s2, mov .a1 .s3, .addi .a2 .s0 ccO, .addi .a3 .s0 bO, .li .a4 1, .addi .a5 .s0 scrO] :
      List Instr)

/-- The first 8 bytes of the block kept at `W + 16 + 8 s11`, the next `s11`,
and `a2` the number of blocks left (`rounds / 2 - 1` of them in all). -/
def derivePost : List Instr :=
  [.load .d .a0 .s0 bO, .shift .sll .d .a1 .s11 3, .add .a1 .s0 .a1, .store .d .a0 .a1 akO, .addi .s11 .s11 1,
    .shift .srl .d .a2 .s3 1, .addi .a2 .a2 (-1), .sub .a2 .a2 .s11]

/-- The message keys, 8 bytes per block, from `W + 16`. -/
def derive : Prog isa :=
  .seq (.block [.li .s11 0])
    (.loop (.seq (.block deriveBlock) (.seq ctrCall (.block derivePost))) (.nonzero .a2))

/-- The arguments of `vg_aes_expand_key_scratch`: the encryption key, whose
length is `4 (rounds − 6)`, its schedule at `W + 256` and the working
space. -/
def expandArgs : List Instr :=
  [.addi .a0 .s0 ekO, .addi .a1 .s3 (-6), .shift .sll .d .a1 .a1 2, .addi .a2 .s0 skO, .addi .a3 .s0 scrO]

/-- The encryption key's schedule at `W + 256`. -/
def expand : Prog isa := .seq (.block expandArgs) keyCall

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number, in the doublewords `a0` and `a1`), in GHASH's order at `W + 64`
(its bytes reversed, stored big-endian), and its accumulator zeroed. -/
def hkey : List Instr :=
  ([.load .d .a0 .s0 akO, .load .d .a1 .s0 (akO + 8), .logicImm .and .a2 .a0 1, .li .a3 0,
    .sub .a2 .a3 .a2, .shift .srl .d .a0 .a0 1, .shift .sll .d .a3 .a1 63, .logic .or .a0 .a0 .a3,
    .shift .srl .d .a1 .a1 1, .li .a3 0xe1, .shift .sll .d .a3 .a3 56, .logic .and .a2 .a2 .a3,
    .logic .xor .a1 .a1 .a2] : List Instr) ++
    storeBE 8 .a1 .t0 .s0 hO ++ storeBE 8 .a0 .t0 .s0 (hO + 8) ++ zero16 yO

/-- The keys and GHASH's key. -/
def keys : Prog isa := .seq derive (.seq expand (.block hkey))

/-! ## POLYVAL -/

/-- `s11 := min (s10 / 16, 64)`. -/
def chunkLen : Prog isa :=
  .seq (.block [.shift .srl .d .s11 .s10 10])
    (.ite (.zero .s11) (.block [.shift .srl .d .s11 .s10 4]) (.block [.li .s11 64]))

/-- The `a3` (at least 1) blocks at `s9` copied to `a4`, the bytes of each
reversed, advancing both. -/
def revLoop : Prog isa :=
  .loop (.block (loadBE64 .a5 .t0 .s9 8 ++ loadBE64 .a6 .t0 .s9 0 ++
    ([.store .d .a5 .a4 0, .store .d .a6 .a4 8, .addi .s9 .s9 16, .addi .a4 .a4 16, .addi .a3 .a3 (-1)] :
      List Instr))) (.nonzero .a3)

/-- After the copies: `s10` past the blocks, and the arguments of
`vg_ghash`. -/
def chunkArgs : List Instr :=
  [.shift .sll .d .a2 .s11 4, .sub .s10 .s10 .a2, .addi .a0 .s0 hO, .addi .a1 .s0 yO, .addi .a2 .s0 revO,
    mov .a3 .s11, .addi .a4 .s0 ghO]

/-- Up to 64 of the whole blocks of the `s10` bytes at `s9` reversed at
`W + 496`, `s9` and `s10` past them, and the arguments of `vg_ghash`. -/
def chunkPre : Prog isa :=
  .seq chunkLen
  (.seq (.block [.addi .a4 .s0 revO, mov .a3 .s11])
  (.seq revLoop (.block chunkArgs)))

/-- `a7` zero iff fewer than 16 of the `s10` bytes are left. -/
def wholeLeft : List Instr := [.shift .srl .d .a7 .s10 4]

/-- Up to 64 of the whole blocks of the `s10` bytes at `s9`, reversed and
absorbed; `s9` and `s10` past them, and `a7` zero if no whole block is
left. -/
def chunk : Prog isa := .seq chunkPre (.seq ghCall (.block wholeLeft))

/-- The last `s10` (1 to 15) bytes at `s9`, padded with zeros at
`W + 240`, as the 16 bytes to absorb. -/
def absTailPre : Prog isa :=
  .seq (.block (zero16 bO ++ ([mov .a0 .s9, .addi .a1 .s0 bO, mov .a2 .s10] : List Instr)))
  (.seq copyLoop (.block [.addi .s9 .s0 bO, .li .s10 16]))

/-- The last `s10` (1 to 15) bytes at `s9`, padded with zeros at
`W + 240`, absorbed. -/
def absTail : Prog isa := .seq absTailPre chunk

/-- The `s10` bytes at `s9`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block wholeLeft)
  (.seq (.ite (.zero .a7) (.block []) (.loop chunk (.nonzero .a7)))
    (.ite (.zero .s10) (.block []) absTail))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, at `W + 240`, as
the bytes to absorb. -/
def lensBlock : List Instr :=
  [.shift .sll .d .a0 .s5 3, .store .d .a0 .s0 bO, .shift .sll .d .a0 .s7 3, .store .d .a0 .s0 (bO + 8),
    .addi .s9 .s0 bO, .li .s10 16]

/-- The lengths block absorbed. -/
def lens : Prog isa := .seq (.block lensBlock) chunk

/-- The tag input at `W + 96`: POLYVAL's result in its own order (the bytes
of the accumulator reversed, loaded big-endian), its first 12 bytes XORed
with the nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  loadBE64 .a0 .t0 .s0 (yO + 8) ++ loadBE64 .a1 .t0 .s0 yO ++
    [.load .d .a2 .s0 nO, .logic .xor .a0 .a0 .a2, .load .w .a2 .s0 (nO + 8), .logic .xor .a1 .a1 .a2,
      .shift .sll .d .a1 .a1 1, .shift .srl .d .a1 .a1 1, .store .d .a0 .s0 cbO, .store .d .a1 .s0 (cbO + 8)]

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block [mov .s9 .s4, mov .s10 .s5])
  (.seq absorb
  (.seq (.block [mov .s9 .s6, mov .s10 .s7])
  (.seq absorb
  (.seq lens (.block tagIn)))))

/-- The encryption of the block at `W + 96` with the encryption key, at
`W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ ([.addi .a3 .s0 o, .li .a4 1] : List Instr))) ctrCall

/-! ## Counter mode -/

/-- The counter block from the tag at `W`, with the top bit of its last
byte set, and the data as the bytes to encrypt; `a7` zero if it has no
whole block. -/
def cryptHead : List Instr :=
  ([mov .s9 .s6, mov .s10 .s7, .load .d .a0 .s0 tagO, .load .d .a1 .s0 (tagO + 8), .li .a2 1,
    .shift .sll .d .a2 .a2 63, .logic .or .a1 .a1 .a2, .store .d .a0 .s0 cbO, .store .d .a1 .s0 (cbO + 8)] :
    List Instr) ++ wholeLeft

/-- After a block: the counter block's first word incremented, `s9` and
`s10` past the block, and `a7` zero if no whole block is left. -/
def blockNext : List Instr :=
  ([.load .w .a0 .s0 cbO, .addi .a0 .a0 1, .store .w .a0 .s0 cbO, .addi .s9 .s9 16, .addi .s10 .s10 (-16)] :
    List Instr) ++ wholeLeft

/-- One block at `s9` encrypted in place from the counter block, which is
then incremented; `s9` and `s10` past it, and `a7` zero if no whole block
is left. -/
def cryptBlock : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ ctrArgs ++ ([mov .a3 .s9, .li .a4 1] : List Instr)))
    (.seq ctrCall (.block blockNext))

/-- The last `s10` (1 to 15) bytes at `s9` XORed with a keystream block,
computed at `W + 240`. -/
def cryptTail : Prog isa :=
  .seq (tag bO) (.seq (.block [.addi .a0 .s0 bO, mov .a1 .s9, mov .a2 .s10]) xorLoop)

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (.ite (.zero .a7) (.block []) (.loop cryptBlock (.nonzero .a7)))
    (.ite (.zero .s10) (.block []) cryptTail))

/-! ## Comparing tags and masking -/

/-- `s11 = 1` if the tags at `W` and `W + 240` are equal, 0 if not, without
a branch (`1 − ((d | −d) >> 63)` for the OR `d` of the XORs of their
doublewords). -/
def cmp : List Instr :=
  [.load .d .a0 .s0 tagO, .load .d .a1 .s0 bO, .logic .xor .a0 .a0 .a1, .load .d .a1 .s0 (tagO + 8),
    .load .d .a2 .s0 (bO + 8), .logic .xor .a1 .a1 .a2, .logic .or .a0 .a0 .a1, .li .a1 0, .sub .a1 .a1 .a0,
    .logic .or .a0 .a0 .a1, .shift .srl .d .a0 .a0 63, .li .s11 1, .sub .s11 .s11 .a0]

/-- One byte of the data ANDed with the mask `a2`. -/
def maskBody : List Instr :=
  [.load .b .t0 .a0 0, .logic .and .t0 .t0 .a2, .store .b .t0 .a0 0, .addi .a0 .a0 1, .addi .a1 .a1 (-1)]

/-- Every byte of the data ANDed with `0 − s11`. -/
def mask : Prog isa :=
  .seq (.block [.li .a2 0, .sub .a2 .a2 .s11, mov .a0 .s6, mov .a1 .s7])
    (.ite (.zero .a1) (.block []) (.loop (.block maskBody) (.nonzero .a1)))

/-! ## The functions -/

/-- Loads `work` from the stack, saves our caller's registers and the
return address in it (keeping `W` in `s0`), keeps the arguments in
`s1`–`s8`, and copies the nonce to `W + 1520`. -/
def entry : List Instr :=
  [.addSp .t1 0, .load .d .t1 .t1 0] ++ save .t1 ++
    [mov .s1 .a2, mov .s2 .a0, mov .s3 .a1, mov .s4 .a3, mov .s5 .a4, mov .s6 .a5, mov .s7 .a6,
      mov .s8 .a7] ++ copyBytes .t0 .s1 .s0 0 nO 12

/-- The received tag copied from `tag` to `W`. -/
def recv : List Instr := copyBytes .t0 .s8 .s0 0 tagO 16

/-- The tag copied from `W` to `tag`. -/
def tagOut : List Instr := copyBytes .t0 .s0 .s8 tagO 0 16

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq keys (.seq polyval (.seq (tag tagO) (.seq crypt (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq keys (.seq crypt (.seq polyval (.seq (tag bO)
    (.seq (.block cmp) (.seq mask (.block ([mov .a0 .s11] ++ restore)))))))))

end VG.Impl.AesGcmSiv.RISCV64
