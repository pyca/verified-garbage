module

public import VerifiedGarbage.Impl.Aes.PPC64LE.Blocks
public import VerifiedGarbage.Impl.AesGcm.PPC64LE

/-!
# AES-OCB: PPC64LE implementation

`vg_aes_ocb_seal(ctx = r3, rounds = r4, nonce = r5, nonce_len = r6,
aad = r7, aad_len = r8, data = r9, len = r10, tag = [sp + 96],
tag_len = [sp + 104], work = [sp + 112])` and `vg_aes_ocb_open` with the
same arguments (`Spec/Ocb/Contract.lean`), with the working space (`work`)
as a last argument, which a frame on the stack allocates
(`Impl.StackScratch.PPC64LE.withStackScratchArgs`), composed of calls of the
verified `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, as on ARMv7
(`Impl/AesOcb/Arm.lean`):

* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
* `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times, computed for each block by
  a loop on the public `i`; `L_$` and `L_0` are `L_*` doubled once and
  twice. A block is doubled as two big-endian doublewords (`ldbrx`,
  `stdbrx`).
* `HASH(K, A)` copies up to 8 blocks of the associated data at a time,
  each XORed with its offset, to `W + bufO`, and enciphers them there.
* `Offset_0` takes the bits `bottom … bottom + 127` of `Stretch` (§4.2),
  where `bottom` is the last 6 bits of the nonce, which is secret: the
  192-bit `Stretch`, in three doublewords, is shifted left by 1, 2, 4, 8, 16
  and 32 bits, each shift kept or not by a mask from a bit of `bottom`.
* `seal` computes the tag at `W` and copies its first `tag_len` bytes to
  `tag` (`tagOut`).
* `open` copies the received tag, padded with zeros, to `W` (`recv`), and
  the first `tag_len` bytes of the tag it computes, padded with zeros, to
  `W + vO`, compares them without a branch (`cmp`) and ANDs every byte of
  the data with `0 − ok` (`mask`).

The key setup, `vg_aes_ocb_init`, is `vg_aes_gcm_init`'s: a key context of
AES-OCB is one of AES-GCM.

## The working space `W` (`work`, 2560 bytes)

`[0, 16)`: the tag (out of `seal`; the received one, for `open`); then the
offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the current
`L_{ntz(i)}` and a block for one call, to 128; our caller's `r18`–`r31` and
our return address at `[128, 248)` (as AES-GCM saves them,
`Impl.AesGcm.PPC64LE.save`); the tag `open` computes, the offset of `HASH`,
`bottom`, the number of blocks of a chunk of `HASH`, the blocks of the
associated data left, `Offset_0` and the tag `open` computes, padded, to
352; `[384, 512)`: 8 blocks of the associated data; `[512, 2560)`: the
working space of the functions called.

## Registers

As in AES-GCM (`Impl.AesGcm.PPC64LE.openEntry`, whose entry this is): `r31`
holds `W` (and `r30` `W + 16`), `r29` the key context, `r28` the number of
rounds, `r21` and `r22` the associated data and its length, `r27` and `r23`
the data and its length, `r20` and `r19` the tag and its length, `r18` the
nonce's length, all of them throughout; the functions called preserve them,
and `r24`–`r26`, which hold a pointer, a count of blocks or bytes and the
block index `i` across calls. `r0`, `r3`–`r12` are temporaries. Only the
pointers, the lengths, `rounds` and `tag_len` (and for `open`, whether the
tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOcb.PPC64LE

open VG.PPC64LE
open VG.Impl.AesGcm.PPC64LE (mov save restore copyLoop xorLoop openEntry)

/-! ## The working space -/

def tagO : Nat := 0
def ofsO : Nat := 16
def ckO : Nat := 32
def sumO : Nat := 48
def ldO : Nat := 64
def l0O : Nat := 80
def lO : Nat := 96
def tmpO : Nat := 112
def t2O : Nat := 256
def ohO : Nat := 272
def botO : Nat := 288
def cnO : Nat := 296
def hlO : Nat := 304
def o0O : Nat := 320
def vO : Nat := 336
def bufO : Nat := 384
def scrO : Nat := 512

/-! ## Blocks -/

/-- `cb + cd ← (pb + pd) ⊕ (qb + qd)`, a doubleword at a time through `r3`
and `r4`. -/
def xorB (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.load .d .r3 pb pd, .load .d .r4 qb qd, .logic .xor .r3 .r3 .r4, .store .d .r3 cb cd,
   .load .d .r3 pb (pd + 8), .load .d .r4 qb (qd + 8), .logic .xor .r3 .r3 .r4, .store .d .r3 cb (cd + 8)]

/-- `W + d ← W + d ⊕ W + s`. -/
def xorW (s d : Nat) : List Instr := xorB .r31 .r31 .r31 d s d

/-- `W + d ← W + s`. -/
def copy16 (s d : Nat) : List Instr :=
  [.load .d .r3 .r31 s, .load .d .r4 .r31 (s + 8), .store .d .r3 .r31 d, .store .d .r4 .r31 (d + 8)]

/-- `W + d ← 0`. -/
def zero16 (d : Nat) : List Instr := [.li .r0 0, .store .d .r0 .r31 d, .store .d .r0 .r31 (d + 8)]

/-- `W + d ← double(b + s)` (§2): the block is big-endian, so it is loaded
as two big-endian doublewords into `r3` (the most significant) and `r4`,
shifted left by one bit, the carry out of `r3` reducing `r4` by `{87}`
through a mask (`(0 − c) ∧ {87}` for the carry `c`), and stored back
big-endian. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  [.li .r0 s, .loadRev .d .r3 b .r0, .li .r0 (s + 8), .loadRev .d .r4 b .r0,
   .lsr .d .r5 .r3 63, .li .r6 0, .sub .r5 .r6 .r5, .li .r6 0x87, .logic .and .r5 .r5 .r6,
   .lsl .r3 .r3 1, .lsr .d .r6 .r4 63, .logic .or .r3 .r3 .r6, .lsl .r4 .r4 1, .logic .xor .r4 .r4 .r5,
   .li .r0 d, .storeRev .d .r3 .r31 .r0, .li .r0 (d + 8), .storeRev .d .r4 .r31 .r0]

/-- `r5 := r12 ∧ 1`. -/
def low1 : List Instr := [.li .r0 1, .logic .and .r5 .r12 .r0]

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `r26`: `L_0` doubled while the low
bit of `r12` (from `i`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ ([mov .r12 .r26] : List Instr) ++ low1))
    (.ite (.zero .d .r5)
      (.loop (.block (dbl .r31 lO lO ++ ([.lsr .d .r12 .r12 1] : List Instr) ++ low1)) (.zero .d .r5))
      (.block []))

/-! ## Calls -/

/-- `vg_aes_encrypt_blocks`. -/
def encCall : Prog isa := .call "vg_aes_encrypt_blocks" Impl.Aes.PPC64LE.encryptBlocks

/-- `vg_aes_decrypt_blocks`. -/
def decCall : Prog isa := .call "vg_aes_decrypt_blocks" Impl.Aes.PPC64LE.decryptBlocks

/-- The arguments of a call but the blocks: the key context's schedule, the
number of rounds and the working space. -/
def callArgs : List Instr := [mov .r3 .r29, mov .r4 .r28, .addi .r7 .r31 scrO]

/-- `ENCIPHER` of the block at `W + d`, in place. -/
def encOne (d : Nat) : Prog isa := .seq (.block (callArgs ++ [.addi .r5 .r31 d, .li .r6 1])) encCall

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := dbl .r29 240 ldO ++ dbl .r31 ldO l0O

/-- `W + d ← pad(S)` (§4.1), `S` the `r25` bytes at `r24`
(`0 < r25 < 16`): zeros, the bytes copied, and `0x80` after them. -/
def padTo (d : Nat) : Prog isa :=
  .seq (.block (zero16 d ++ [.addi .r4 .r31 d, mov .r3 .r24, mov .r5 .r25]))
    (.seq copyLoop (.block [.li .r0 0x80, .stb .r0 .r4 0]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`, for the `r25` bytes of nonce at `r24` and `tag_len` in `r19`:
zeros, the 1 in the byte before where the nonce goes, the nonce's bytes
copied to the end of the block, and `TAGLEN`'s bits in the top of the first
byte. Then `bottom` (its last 6 bits) to `W + botO`, and those bits
cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero16 tmpO ++ [.addi .r4 .r31 (tmpO + 15), .sub .r4 .r4 .r25, .li .r0 1, .stb .r0 .r4 0,
      .addi .r4 .r4 1, mov .r3 .r24, mov .r5 .r25]))
    (.seq copyLoop
      (.block [.li .r0 15, .logic .and .r3 .r19 .r0, .lsl .r3 .r3 4, .lbz .r4 .r31 tmpO,
        .logic .or .r4 .r4 .r3, .stb .r4 .r31 tmpO, .lbz .r4 .r31 (tmpO + 15), .li .r0 63,
        .logic .and .r3 .r4 .r0, .store .d .r3 .r31 botO, .li .r0 0xc0, .logic .and .r4 .r4 .r0,
        .stb .r4 .r31 (tmpO + 15)]))

/-- `r7 := 0 − bit k of bottom` (in `r6`): all ones if it is set. -/
def stageMask (k : Nat) : List Instr :=
  (if k = 0 then [.li .r0 1, .logic .and .r7 .r6 .r0] else [.lsr .d .r7 .r6 k, .li .r0 1, .logic .and .r7 .r7 .r0]) ++
    ([.li .r8 0, .sub .r7 .r8 .r7] : List Instr)

/-- `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, `x'` in `r8`: `x'` if the mask (in `r7`) is
all ones, `x` if it is zero. -/
def sel (x : Reg) : List Instr := [.logic .xor .r8 .r8 x, .logic .and .r8 .r8 .r7, .logic .xor x x .r8]

/-- One stage of the shift of `Stretch` (in `r3`–`r5`, high to low): shifted
left by `a` (from 1 to 32) bits if bit `k` of `bottom` (in `r6`) is set, a
doubleword at a time from the high one, `x' = (x ⋘ a) ∨ (next ⋙ (64 − a))`. -/
def stage (k a : Nat) : List Instr :=
  stageMask k ++
  ([(Reg.r3, Reg.r4), (.r4, .r5)].flatMap fun (x, y) =>
    ([.lsl .r8 x a, .lsr .d .r9 y (64 - a), .logic .or .r8 .r8 .r9] : List Instr) ++ sel x) ++
  ([.lsl .r8 .r5 a] : List Instr) ++ sel .r5

/-- `Offset_0` from `Ktop` at `W + tmpO` and `bottom` at `W + botO`, to
`W + ofsO` and `W + o0O`: `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`
in `r3`–`r5`, shifted left by `bottom`, of which the high 128 bits. -/
def offset0 : List Instr :=
  ([.li .r0 tmpO, .loadRev .d .r3 .r31 .r0, .li .r0 (tmpO + 8), .loadRev .d .r4 .r31 .r0,
   .lsl .r5 .r3 8, .lsr .d .r8 .r4 56, .logic .or .r5 .r5 .r8, .logic .xor .r5 .r5 .r3,
   .load .d .r6 .r31 botO] : List Instr) ++
  stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage 5 32 ++
  ([.li .r0 ofsO, .storeRev .d .r3 .r31 .r0, .li .r0 (ofsO + 8), .storeRev .d .r4 .r31 .r0,
   .li .r0 o0O, .storeRev .d .r3 .r31 .r0, .li .r0 (o0O + 8), .storeRev .d .r4 .r31 .r0] : List Instr)

/-- `Offset_0`, for the `r25` bytes of nonce at `r24`. -/
def nonce : Prog isa := .seq nonceBlock (.seq (encOne tmpO) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `r24`) XORed with its offset to
`r11` (from `W + bufO`, counting up, while `r25` counts down), `i` in
`r26`. -/
def hashFill : Prog isa :=
  .seq lNtz
    (.block (xorW lO ohO ++ xorB .r24 .r31 .r11 0 ohO 0 ++
      [.addi .r11 .r11 16, .addi .r24 .r24 16, .addi .r26 .r26 1, .subi .r25 .r25 1]))

/-- Add the blocks at `W + bufO` to the sum, `r25` of them (counting down,
with `r11` from `W + bufO`). -/
def hashSum : Prog isa :=
  .loop (.block (xorB .r31 .r11 .r31 sumO 0 sumO ++ [.addi .r11 .r11 16, .subi .r25 .r25 1])) (.nonzero .d .r25)

/-- A chunk of `min(8, left)` blocks, `left` the blocks left (at
`W + hlO`; the chunk's at `W + cnO`): fill, encipher, add; `r3` the blocks
left after it. -/
def hashChunk : Prog isa :=
  .seq (.block [.load .d .r3 .r31 hlO, .lsr .d .r4 .r3 3])
  (.seq (.ite (.zero .d .r4) (.block [mov .r25 .r3]) (.block [.li .r25 8]))
  (.seq (.block [.store .d .r25 .r31 cnO, .load .d .r3 .r31 hlO, .sub .r3 .r3 .r25, .store .d .r3 .r31 hlO,
      .addi .r11 .r31 bufO])
  (.seq (.loop hashFill (.nonzero .d .r25))
  (.seq (.block (callArgs ++ [.addi .r5 .r31 bufO, .load .d .r6 .r31 cnO]))
  (.seq encCall
  (.seq (.block [.addi .r11 .r31 bufO, .load .d .r25 .r31 cnO])
  (.seq hashSum (.block [.load .d .r3 .r31 hlO]))))))))

/-- The rest of the associated data (`r25` bytes at `r24`), padded, XORed
with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (xorB .r31 .r29 .r31 ohO 240 ohO))
    (.seq (padTo bufO)
      (.seq (.block (xorW ohO bufO))
        (.seq (encOne bufO) (.block (xorW bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `r21` and
`r22`. -/
def hash : Prog isa :=
  .seq (.block (zero16 sumO ++ zero16 ohO ++
      ([mov .r24 .r21, .lsr .d .r3 .r22 4, .store .d .r3 .r31 hlO, .li .r26 1] : List Instr)))
    (.seq (.ite (.zero .d .r3) (.block []) (.loop hashChunk (.nonzero .d .r3)))
      (.seq (.block [.li .r0 15, .logic .and .r25 .r22 .r0])
        (.ite (.zero .d .r25) (.block []) hashRest)))

/-! ## The whole blocks -/

/-- The offset of block `i` (in `r26`): `Offset ← Offset ⊕ L_{ntz(i)}`. -/
def nextOffset : Prog isa := .seq lNtz (.block (xorW lO ofsO))

/-- `W + ckO ⊕= (r24)`. -/
def addCk : List Instr := xorB .r31 .r24 .r31 ckO 0 ckO

/-- `(r24) ⊕= W + ofsO`. -/
def xorOfs : List Instr := xorB .r24 .r31 .r24 0 ofsO 0

/-- On to the next block (`r25` is zero when none are left). -/
def nextBlock : List Instr := [.addi .r24 .r24 16, .addi .r26 .r26 1, .subi .r25 .r25 1]

/-- A pass over the `r25` whole blocks of the data at `r24` (`r25 > 0`),
with `i` from 1 in `r26`: each block through `body` after its offset. -/
def pass (body : List Instr) : Prog isa :=
  .loop (.seq nextOffset (.block (body ++ nextBlock))) (.nonzero .d .r25)

/-- The start of a pass over the whole blocks of the data (`len >> 4` of
them, at `data`). -/
def passStart : List Instr := [mov .r24 .r27, .lsr .d .r25 .r23 4, .li .r26 1]

/-- The whole blocks: `pre` (the first pass), `f` on all of them, `post` (the
third pass, the offsets recomputed from `Offset_0`). -/
def whole (f : Prog isa) (pre post : List Instr) : Prog isa :=
  .seq (.block passStart)
    (.seq (pass pre)
      (.seq (.block (callArgs ++ ([mov .r5 .r27, .lsr .d .r6 .r23 4] : List Instr)))
        (.seq f
          (.seq (.block (copy16 o0O ofsO ++ passStart))
            (pass post)))))

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `r25` bytes at `r24`
(`0 < r25 < 16`), and add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O) (.block (xorW t2O ckO))

/-- The `r25` bytes at `r24` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa := .seq (.block [.addi .r3 .r31 tmpO, mov .r4 .r24, mov .r5 .r25]) xorLoop

/-- The rest of the data (`r25` bytes at `r24`, `r25 > 0`): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the
checksum of the plaintext, then the XOR; for `open`, the XOR, then the
checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (xorB .r31 .r29 .r31 ofsO 240 ofsO ++ copy16 ofsO tmpO))
    (.seq (encOne tmpO)
      (if enc then .seq padCk xorPad else .seq xorPad padCk))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to
`W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block (copy16 ckO tmpO ++ xorW ofsO tmpO ++ xorW ldO tmpO))
    (.seq (encOne tmpO)
      (.block (copy16 tmpO d ++ xorW sumO d)))

/-! ## The functions -/

/-- The entry: AES-GCM's (`openEntry`: our caller's registers saved in `W`,
the arguments kept), then `L_$` and `L_0`, the checksum zeroed. -/
def entry : List Instr := openEntry ++ lsetup ++ zero16 ckO

/-- The data: whole blocks, then the rest. -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [.lsr .d .r3 .r23 4])
    (.seq (.ite (.zero .d .r3) (.block [])
        (if enc then whole encCall (addCk ++ xorOfs) xorOfs else whole decCall xorOfs (xorOfs ++ addCk)))
      (.seq (.block [.li .r0 15, .logic .and .r25 .r23 .r0, .sub .r24 .r23 .r25, .add .r24 .r24 .r27])
        (.ite (.zero .d .r25) (.block []) (rest enc))))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`: the entry,
`Offset_0`, `HASH`, the data and the tag. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq (.block entry) (.seq nonce (.seq hash (.seq (body enc) (tag d))))

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [mov .r3 .r31, mov .r4 .r20, mov .r5 .r19]) copyLoop

def «seal» : Prog isa := .seq (front true tagO) (.seq tagOut (.block restore))

/-- The received tag, the `tag_len` bytes at `tag`, padded with zeros at `W`. -/
def recv : Prog isa :=
  .seq (.block (zero16 tagO ++ ([mov .r3 .r20, mov .r4 .r31, mov .r5 .r19] : List Instr))) copyLoop

/-- `r3 = 1` if the padded tags at `W` and `W + vO` are equal, 0 if not,
without a branch (`1 - ((x | -x) >> 63)` of the OR `x` of the XORs of their
doublewords). -/
def cmpTail : List Instr :=
  [.load .d .r3 .r31 tagO, .load .d .r4 .r31 vO, .logic .xor .r3 .r3 .r4, .load .d .r4 .r31 (tagO + 8),
   .load .d .r5 .r31 (vO + 8), .logic .xor .r4 .r4 .r5, .logic .or .r3 .r3 .r4, .li .r4 0,
   .sub .r4 .r4 .r3, .logic .or .r3 .r3 .r4, .lsr .d .r3 .r3 63, .li .r4 1, .sub .r3 .r4 .r3]

/-- The first `tag_len` bytes of the tag at `W + t2O`, padded with zeros at
`W + vO`, compared with the received one: `r3 = 1` if they are equal. -/
def cmp : Prog isa :=
  .seq (.block (zero16 vO ++ [.addi .r3 .r31 t2O, .addi .r4 .r31 vO, mov .r5 .r19]))
    (.seq copyLoop (.block cmpTail))

/-- Every byte of the data ANDed with `0 − r3`. -/
def mask : Prog isa :=
  .seq (.block [mov .r24 .r27, mov .r25 .r23, .li .r4 0, .sub .r7 .r4 .r3])
    (.ite (.zero .d .r25) (.block [])
      (.loop (.block [.lbz .r4 .r24 0, .logic .and .r4 .r4 .r7, .stb .r4 .r24 0, .addi .r24 .r24 1,
        .subi .r25 .r25 1]) (.nonzero .d .r25)))

def «open» : Prog isa :=
  .seq (front false t2O) (.seq recv (.seq cmp (.seq mask (.block restore))))

end VG.Impl.AesOcb.PPC64LE
