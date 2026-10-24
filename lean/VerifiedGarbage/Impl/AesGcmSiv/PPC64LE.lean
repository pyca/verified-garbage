module

public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-GCM-SIV: PPC64LE implementation

`vg_aes_gcm_siv_seal` and `vg_aes_gcm_siv_open` (`Spec/GcmSiv/Contract.lean`),
with the working space `work` as a last argument, which a frame on the
stack allocates (`Impl.StackScratch.PPC64LE.withStackScratchArgs`), composed
of calls of the verified `vg_aes_ctr32`, `vg_aes_expand_key_scratch` and
`vg_ghash`, as on ARMv7 (`Impl/AesGcmSiv/Arm.lean`):

* The message keys (RFC 8452 §4): `CIPH_K(little_endian_uint32(i) ‖ nonce)`
  for `i` from 0 to `rounds / 2 - 2` (3 for 10 rounds, 5 for 14), each by
  `vg_aes_ctr32` on a zero block, of which the first 8 bytes are kept, one
  after the other from `W + 16` (`derive`): the authentication key at
  `W + 16`, the encryption key at `W + 32`; the encryption key is expanded
  for the same number of rounds (`expand`).
* POLYVAL (§3) is GHASH on the same bits (`Proof.GcmSiv.Polyval`) with the
  key `H · x` (`hkey`), on blocks in the other byte order: up to 64 blocks
  at a time are copied to `W + 496` with their bytes reversed (`ldbrx`)
  before `vg_ghash` absorbs them (`chunk`). The last bytes of a string,
  padded with zeros, and the lengths block are put in the block at
  `W + 240` and absorbed the same way (`absorb`, `lens`); the result is read
  back reversed (`tagIn`).
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

A call (`bl`) stores nothing in memory and the callees use no stack.

## The working space `W` (3824 bytes)

* `[0, 16)`: the tag (the one `seal` computes, or the received one);
  `[16, 32)`: the authentication key; `[32, 64)`: the encryption key;
  `[64, 80)`: GHASH's key; `[80, 96)`: its accumulator; `[96, 112)`: the
  counter block (or the tag input); `[112, 128)`: a copy of it for a call;
  `[128, 224)`: our caller's `r14`–`r25`, and `[224, 232)` our return
  address; `[240, 256)`: a block (and the tag `open` computes);
* `[256, 496)`: the encryption key's schedule; `[496, 1520)`: the reversed
  blocks; `[1520, 1776)`: `vg_ghash`'s working space; `[1776, 3824)`:
  `vg_aes_ctr32`'s, and `vg_aes_expand_key_scratch`'s at its start.

## Registers

`(schedule = r3, rounds = r4, nonce = r5, aad = r6, aad_len = r7, data = r8,
len = r9, tag = r10, work = [sp + 96])`. The entry keeps `W` in `r14` and
the arguments in `r15`–`r22` (`nonce`, `schedule`, `rounds`, `aad`,
`aad_len`, `data`, `len`, `tag`), which the functions called preserve. The
pieces take a pointer in `r23` and a number of bytes in `r24`, which the
callees also preserve, and `derive` and `chunk` a count in `r25`; `open`
keeps the result of the comparison there. `r0` and `r3`–`r12` are
temporaries.

The model has no indexed byte access and branches only on whether a
register is zero: the bytes are copied, XORed and masked through advancing
pointers, counting down to zero. Only the pointers, the lengths and `rounds`
affect timing.
-/

@[expose] public section

namespace VG.Impl.AesGcmSiv.PPC64LE

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov ctrCall ghCall keyCall copyLoop xorLoop)

def tagO : Nat := 0
def akO : Nat := 16
def ekO : Nat := 32
def hO : Nat := 64
def yO : Nat := 80
def cbO : Nat := 96
def ccO : Nat := 112
def lrO : Nat := 224
def bO : Nat := 240
def skO : Nat := 256
def revO : Nat := 496
def ghO : Nat := 1520
def scrO : Nat := 1776

/-- Our caller's registers, and where we save them (`r14`, the base, last). -/
def saved : List (Reg × Nat) :=
  [(.r15, 136), (.r16, 144), (.r17, 152), (.r18, 160), (.r19, 168), (.r20, 176), (.r21, 184),
    (.r22, 192), (.r23, 200), (.r24, 208), (.r25, 216), (.r14, 128)]

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [.li .r0 0, .store .d .r0 .r14 d, .store .d .r0 .r14 (d + 8)]

/-- The 16 bytes at `W + s` copied to `W + d`. -/
def copy16 (s d : Nat) : List Instr :=
  [.load .d .r3 .r14 s, .load .d .r4 .r14 (s + 8), .store .d .r3 .r14 d, .store .d .r4 .r14 (d + 8)]

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the encryption key's schedule, the counter block's copy at `W + 112` and the
working space. -/
def ctrArgs : List Instr := [.addi .r3 .r14 skO, mov .r4 .r17, .addi .r5 .r14 ccO, .addi .r8 .r14 scrO]

/-! ## The keys -/

/-- `little_endian_uint32(r25) ‖ nonce` at `W + 112`, a zero block at
`W + 240`, and the arguments of `vg_aes_ctr32` with the key-generating key's
schedule. -/
def deriveBlock : List Instr :=
  ([.load .w .r3 .r15 0, .load .w .r4 .r15 4, .load .w .r5 .r15 8, .store .w .r25 .r14 ccO,
    .store .w .r3 .r14 (ccO + 4), .store .w .r4 .r14 (ccO + 8), .store .w .r5 .r14 (ccO + 12)] : List Instr) ++
    zero16 bO ++
    ([mov .r3 .r16, mov .r4 .r17, .addi .r5 .r14 ccO, .addi .r6 .r14 bO, .li .r7 1, .addi .r8 .r14 scrO] :
      List Instr)

/-- The first 8 bytes of the block kept at `W + 16 + 8 r25`, the next `r25`,
and `r5` the number of blocks left (`rounds / 2 - 1` of them in all). -/
def derivePost : List Instr :=
  [.load .d .r3 .r14 bO, .lsl .r4 .r25 3, .add .r4 .r14 .r4, .store .d .r3 .r4 akO, .addi .r25 .r25 1,
    .lsr .d .r5 .r17 1, .subi .r5 .r5 1, .sub .r5 .r5 .r25]

/-- The message keys, 8 bytes per block, from `W + 16`. -/
def derive : Prog isa :=
  .seq (.block [.li .r25 0])
    (.loop (.seq (.block deriveBlock) (.seq ctrCall (.block derivePost))) (.nonzero .d .r5))

/-- The arguments of `vg_aes_expand_key_scratch`: the encryption key, whose
length is `4 (rounds − 6)`, its schedule at `W + 256` and the working
space. -/
def expandArgs : List Instr :=
  [.addi .r3 .r14 ekO, .subi .r4 .r17 6, .lsl .r4 .r4 2, .addi .r5 .r14 skO, .addi .r6 .r14 scrO]

/-- The encryption key's schedule at `W + 256`. -/
def expand : Prog isa := .seq (.block expandArgs) keyCall

/-- GHASH's key, `H · x` for the authentication key `H` (as a little-endian
number, in the doublewords `r3` and `r4`), in GHASH's order at `W + 64`
(its bytes reversed, `stdbrx`), and its accumulator zeroed. -/
def hkey : List Instr :=
  ([.load .d .r3 .r14 akO, .load .d .r4 .r14 (akO + 8), .li .r5 1, .logic .and .r5 .r3 .r5, .li .r6 0,
    .sub .r5 .r6 .r5, .lsr .d .r3 .r3 1, .lsl .r6 .r4 63, .logic .or .r3 .r3 .r6, .lsr .d .r4 .r4 1,
    .lis .r6 0xe100, .lsl .r6 .r6 32, .logic .and .r5 .r5 .r6, .logic .xor .r4 .r4 .r5,
    .li .r7 hO, .storeRev .d .r4 .r14 .r7, .li .r7 (hO + 8), .storeRev .d .r3 .r14 .r7] : List Instr) ++
    zero16 yO

/-- The keys and GHASH's key. -/
def keys : Prog isa := .seq derive (.seq expand (.block hkey))

/-! ## POLYVAL -/

/-- `r25 := min (r24 / 16, 64)`. -/
def chunkLen : Prog isa :=
  .seq (.block [.lsr .d .r25 .r24 10])
    (.ite (.zero .d .r25) (.block [.lsr .d .r25 .r24 4]) (.block [.li .r25 64]))

/-- The `r3` (at least 1) blocks at `r23` copied to `r4`, the bytes of each
reversed (`r9` holding 8 and `r10` 0), advancing both. -/
def revLoop : Prog isa :=
  .loop (.block [.loadRev .d .r5 .r23 .r9, .loadRev .d .r6 .r23 .r10, .store .d .r5 .r4 0,
    .store .d .r6 .r4 8, .addi .r23 .r23 16, .addi .r4 .r4 16, .subi .r3 .r3 1]) (.nonzero .d .r3)

/-- After the copies: `r24` past the blocks, and the arguments of
`vg_ghash`. -/
def chunkArgs : List Instr :=
  [.lsl .r5 .r25 4, .sub .r24 .r24 .r5, .addi .r3 .r14 hO, .addi .r4 .r14 yO, .addi .r5 .r14 revO,
    mov .r6 .r25, .addi .r7 .r14 ghO]

/-- Up to 64 of the whole blocks of the `r24` bytes at `r23` reversed at
`W + 496`, `r23` and `r24` past them, and the arguments of `vg_ghash`. -/
def chunkPre : Prog isa :=
  .seq chunkLen
  (.seq (.block [.addi .r4 .r14 revO, mov .r3 .r25, .li .r9 8, .li .r10 0])
  (.seq revLoop (.block chunkArgs)))

/-- `r11` zero iff fewer than 16 of the `r24` bytes are left. -/
def wholeLeft : List Instr := [.lsr .d .r11 .r24 4]

/-- Up to 64 of the whole blocks of the `r24` bytes at `r23`, reversed and
absorbed; `r23` and `r24` past them, and `r11` zero if no whole block is
left. -/
def chunk : Prog isa := .seq chunkPre (.seq ghCall (.block wholeLeft))

/-- The last `r24` (1 to 15) bytes at `r23`, padded with zeros at
`W + 240`, as the 16 bytes to absorb. -/
def absTailPre : Prog isa :=
  .seq (.block (zero16 bO ++ ([mov .r3 .r23, .addi .r4 .r14 bO, mov .r5 .r24] : List Instr)))
  (.seq copyLoop (.block [.addi .r23 .r14 bO, .li .r24 16]))

/-- The last `r24` (1 to 15) bytes at `r23`, padded with zeros at
`W + 240`, absorbed. -/
def absTail : Prog isa := .seq absTailPre chunk

/-- The `r24` bytes at `r23`, padded with zeros to whole blocks, absorbed. -/
def absorb : Prog isa :=
  .seq (.block wholeLeft)
  (.seq (.ite (.zero .d .r11) (.block []) (.loop chunk (.nonzero .d .r11)))
    (.ite (.zero .d .r24) (.block []) absTail))

/-- The lengths block, `le64(8 · aad_len) ‖ le64(8 · len)`, at `W + 240`, as
the bytes to absorb. -/
def lensBlock : List Instr :=
  [.lsl .r3 .r19 3, .store .d .r3 .r14 bO, .lsl .r3 .r21 3, .store .d .r3 .r14 (bO + 8), .addi .r23 .r14 bO,
    .li .r24 16]

/-- The lengths block absorbed. -/
def lens : Prog isa := .seq (.block lensBlock) chunk

/-- The tag input at `W + 96`: POLYVAL's result in its own order (the bytes
of the accumulator reversed, `ldbrx`), its first 12 bytes XORed with the
nonce and the top bit of its last byte cleared. -/
def tagIn : List Instr :=
  [.li .r9 (yO + 8), .loadRev .d .r3 .r14 .r9, .li .r9 yO, .loadRev .d .r4 .r14 .r9, .load .d .r5 .r15 0,
    .logic .xor .r3 .r3 .r5, .load .w .r5 .r15 8, .logic .xor .r4 .r4 .r5, .lsl .r4 .r4 1, .lsr .d .r4 .r4 1,
    .store .d .r3 .r14 cbO, .store .d .r4 .r14 (cbO + 8)]

/-- POLYVAL of the additional data, the data and the lengths, and the tag
input. -/
def polyval : Prog isa :=
  .seq (.block [mov .r23 .r18, mov .r24 .r19])
  (.seq absorb
  (.seq (.block [mov .r23 .r20, mov .r24 .r21])
  (.seq absorb
  (.seq lens (.block tagIn)))))

/-- The encryption of the block at `W + 96` with the encryption key, at
`W + o`. -/
def tag (o : Nat) : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ zero16 o ++ ctrArgs ++ ([.addi .r6 .r14 o, .li .r7 1] : List Instr))) ctrCall

/-! ## Counter mode -/

/-- The counter block from the tag at `W`, with the top bit of its last
byte set, and the data as the bytes to encrypt; `r11` zero if it has no
whole block. -/
def cryptHead : List Instr :=
  ([mov .r23 .r20, mov .r24 .r21, .load .d .r3 .r14 tagO, .load .d .r4 .r14 (tagO + 8), .li .r5 1,
    .lsl .r5 .r5 63, .logic .or .r4 .r4 .r5, .store .d .r3 .r14 cbO, .store .d .r4 .r14 (cbO + 8)] :
    List Instr) ++ wholeLeft

/-- After a block: the counter block's first word incremented, `r23` and
`r24` past the block, and `r11` zero if no whole block is left. -/
def blockNext : List Instr :=
  ([.load .w .r3 .r14 cbO, .addi .r3 .r3 1, .store .w .r3 .r14 cbO, .addi .r23 .r23 16, .subi .r24 .r24 16] :
    List Instr) ++ wholeLeft

/-- One block at `r23` encrypted in place from the counter block, which is
then incremented; `r23` and `r24` past it, and `r11` zero if no whole block
is left. -/
def cryptBlock : Prog isa :=
  .seq (.block (copy16 cbO ccO ++ ctrArgs ++ ([mov .r6 .r23, .li .r7 1] : List Instr)))
    (.seq ctrCall (.block blockNext))

/-- The last `r24` (1 to 15) bytes at `r23` XORed with a keystream block,
computed at `W + 240`. -/
def cryptTail : Prog isa :=
  .seq (tag bO) (.seq (.block [.addi .r3 .r14 bO, mov .r4 .r23, mov .r5 .r24]) xorLoop)

/-- The data encrypted (or decrypted) in place, from the tag at `W` with the
top bit of its last byte set. -/
def crypt : Prog isa :=
  .seq (.block cryptHead)
  (.seq (.ite (.zero .d .r11) (.block []) (.loop cryptBlock (.nonzero .d .r11)))
    (.ite (.zero .d .r24) (.block []) cryptTail))

/-! ## Comparing tags and masking -/

/-- `r25 = 1` if the tags at `W` and `W + 240` are equal, 0 if not, without
a branch (`1 − ((d | −d) >> 63)` for the OR `d` of the XORs of their
doublewords). -/
def cmp : List Instr :=
  [.load .d .r3 .r14 tagO, .load .d .r4 .r14 bO, .logic .xor .r3 .r3 .r4, .load .d .r4 .r14 (tagO + 8),
    .load .d .r5 .r14 (bO + 8), .logic .xor .r4 .r4 .r5, .logic .or .r3 .r3 .r4, .li .r4 0, .sub .r4 .r4 .r3,
    .logic .or .r3 .r3 .r4, .lsr .d .r3 .r3 63, .li .r25 1, .sub .r25 .r25 .r3]

/-- One byte of the data ANDed with the mask `r9`. -/
def maskBody : List Instr :=
  [.lbz .r0 .r3 0, .logic .and .r0 .r0 .r9, .stb .r0 .r3 0, .addi .r3 .r3 1, .subi .r4 .r4 1]

/-- Every byte of the data ANDed with `0 − r25`. -/
def mask : Prog isa :=
  .seq (.block [.li .r9 0, .sub .r9 .r9 .r25, mov .r3 .r20, mov .r4 .r21])
    (.ite (.zero .d .r4) (.block []) (.loop (.block maskBody) (.nonzero .d .r4)))

/-! ## The functions -/

/-- Loads `work` from the stack, saves our caller's registers and the
return address in it, and keeps the arguments in `r15`–`r22` and `W` in
`r14`. -/
def entry : List Instr :=
  [.addSp .r12 0, .load .d .r11 .r12 96, .mflr .r0] ++ saved.map (fun (r, d) => .store .d r .r11 d) ++
    [.store .d .r0 .r11 lrO, mov .r14 .r11, mov .r15 .r5, mov .r16 .r3, mov .r17 .r4, mov .r18 .r6,
      mov .r19 .r7, mov .r20 .r8, mov .r21 .r9, mov .r22 .r10]

/-- Restores the return address and our caller's registers (`r14`, the base,
last). -/
def restore : List Instr :=
  [.load .d .r0 .r14 lrO, .mtlr .r0] ++ saved.map (fun (r, d) => .load .d r .r14 d)

/-- The received tag copied from `tag` to `W`. -/
def recv : List Instr :=
  [.load .d .r3 .r22 0, .load .d .r4 .r22 8, .store .d .r3 .r14 tagO, .store .d .r4 .r14 (tagO + 8)]

/-- The tag copied from `W` to `tag`. -/
def tagOut : List Instr :=
  [.load .d .r3 .r14 tagO, .load .d .r4 .r14 (tagO + 8), .store .d .r3 .r22 0, .store .d .r4 .r22 8]

/-- `vg_aes_gcm_siv_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq keys (.seq polyval (.seq (tag tagO) (.seq crypt (.block (tagOut ++ restore))))))

/-- `vg_aes_gcm_siv_open`. -/
def «open» : Prog isa :=
  .seq (.block entry) (.seq (.block recv) (.seq keys (.seq crypt (.seq polyval (.seq (tag bO)
    (.seq (.block cmp) (.seq mask (.block ([mov .r3 .r25] ++ restore)))))))))

end VG.Impl.AesGcmSiv.PPC64LE
