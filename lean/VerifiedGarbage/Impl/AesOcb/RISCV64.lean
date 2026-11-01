module

public import VerifiedGarbage.Impl.Aes.RISCV64.Blocks
public import VerifiedGarbage.Impl.AesGcm.RISCV64

/-!
# AES-OCB: RISC-V implementation

`vg_aes_ocb_seal(ctx = a0, rounds = a1, nonce = a2, nonce_len = a3,
aad = a4, aad_len = a5, data = a6, len = a7, tag = [sp], tag_len = [sp + 8],
work = [sp + 16])` and `vg_aes_ocb_open` with the same arguments
(`Spec/Ocb/Contract.lean`), with the working space (`work`) as a last
argument, which a frame on the stack allocates
(`Impl.StackScratch.RISCV64.withStackScratchArgs`), composed of calls of the
verified `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, as on PPC64LE
(`Impl/AesOcb/PPC64LE.lean`), piece for piece:

* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
* `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times, computed for each block by
  a loop on the public `i`; `L_$` and `L_0` are `L_*` doubled once and
  twice. A block is doubled as two big-endian doublewords, loaded and
  stored a byte at a time (`loadBE64`, `storeBE`).
* `HASH(K, A)` copies up to 8 blocks of the associated data at a time to
  `W + bufO`, each XORed with its offset, and enciphers them there.
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

Loads and stores fault unless naturally aligned, and the contracts state no
alignment for the nonce, the associated data, the data and the tag: their
bytes are copied, or XORed in, a byte at a time (`copyLoop`, `xorLoop`), and
a block of them added to a block of `W` is first copied to `W` (`addCk`,
`hashFill`). `W` and the key context are aligned.

## The working space `W` (`work`, 2560 bytes)

As on PPC64LE: `[0, 16)` the tag (out of `seal`; the received one, for
`open`); then the offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the
current `L_{ntz(i)}` and a block for one call, to 128; our caller's
`s0`–`s11` and our return address at `[128, 232)`, and the addresses of the
associated data and the data at 232 and 240 (as AES-GCM saves them,
`Impl.AesGcm.RISCV64.oneEntry`); a block of the data (or the tag `open`
computes), the offset of `HASH`, `bottom`, the number of blocks of a chunk of
`HASH`, the blocks of the associated data left, `Offset_0` and the tag
`open` computes, padded, to 352; `[384, 512)`: 8 blocks of the associated
data; `[512, 2560)`: the working space of the functions called.

## Registers

As in AES-GCM (`Impl.AesGcm.RISCV64.openEntry`, whose entry this is): `s0`
holds `W`, `s2` the key context, `s3` the number of rounds, `s10` the length
of the associated data, `s11` the length of the data, `s9` and `s8` the tag
and its length, `s7` the nonce's length, all of them throughout; the
functions called preserve them, and `s4`–`s6`, which hold a pointer, a count
of blocks or bytes and the block index `i` across calls. `a0`–`a7` and
`t0`–`t6` are temporaries. Only the pointers, the lengths, `rounds` and
`tag_len` (and for `open`, whether the tag is right) affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOcb.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (loadBE64 storeBE)
open VG.Impl.AesGcm.RISCV64 (mov save restore copyLoop xorLoop openEntry aadO dataO)

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

/-- `cb + cd ← (pb + pd) ⊕ (qb + qd)`, a doubleword at a time through `t1`
and `t2`, for aligned blocks. -/
def xorB (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.load .d .t1 pb pd, .load .d .t2 qb qd, .logic .xor .t1 .t1 .t2, .store .d .t1 cb cd,
   .load .d .t1 pb (pd + 8), .load .d .t2 qb (qd + 8), .logic .xor .t1 .t1 .t2, .store .d .t1 cb (cd + 8)]

/-- `W + d ← W + d ⊕ W + s`. -/
def xorW (s d : Nat) : List Instr := xorB .s0 .s0 .s0 d s d

/-- `W + d ← W + s`. -/
def copy16 (s d : Nat) : List Instr :=
  [.load .d .t1 .s0 s, .load .d .t2 .s0 (s + 8), .store .d .t1 .s0 d, .store .d .t2 .s0 (d + 8)]

/-- `W + d ← 0`. -/
def zero16 (d : Nat) : List Instr := [.li .t0 0, .store .d .t0 .s0 d, .store .d .t0 .s0 (d + 8)]

/-- `W + d ← double(b + s)` (§2): the block is big-endian, so it is loaded
as two big-endian doublewords into `t1` (the most significant) and `t2`,
shifted left by one bit, the carry out of `t1` reducing `t2` by `{87}`
through a mask (`(0 − c) ∧ {87}` for the carry `c`), and stored back
big-endian. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  loadBE64 .t1 .t0 b s ++ loadBE64 .t2 .t0 b (s + 8) ++
  [.shift .srl .d .t3 .t1 63, .li .t4 0, .sub .t3 .t4 .t3, .li .t4 0x87, .logic .and .t3 .t3 .t4,
   .shift .sll .d .t1 .t1 1, .shift .srl .d .t4 .t2 63, .logic .or .t1 .t1 .t4, .shift .sll .d .t2 .t2 1,
   .logic .xor .t2 .t2 .t3] ++
  storeBE 8 .t1 .t0 .s0 d ++ storeBE 8 .t2 .t0 .s0 (d + 8)

/-- `t3 := a5 ∧ 1`. -/
def low1 : List Instr := [.logicImm .and .t3 .a5 1]

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `s6`: `L_0` doubled while the low
bit of `a5` (from `i`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ ([mov .a5 .s6] : List Instr) ++ low1))
    (.ite (.zero .t3)
      (.loop (.block (dbl .s0 lO lO ++ ([.shift .srl .d .a5 .a5 1] : List Instr) ++ low1)) (.zero .t3))
      (.block []))

/-! ## Calls -/

/-- `vg_aes_encrypt_blocks`. -/
def encCall : Prog isa := .call "vg_aes_encrypt_blocks" Impl.Aes.RISCV64.encryptBlocks

/-- `vg_aes_decrypt_blocks`. -/
def decCall : Prog isa := .call "vg_aes_decrypt_blocks" Impl.Aes.RISCV64.decryptBlocks

/-- The arguments of a call but the blocks: the key context's schedule, the
number of rounds and the working space. -/
def callArgs : List Instr := [mov .a0 .s2, mov .a1 .s3, .addi .a4 .s0 (scrO : Int)]

/-- `ENCIPHER` of the block at `W + d`, in place. -/
def encOne (d : Nat) : Prog isa := .seq (.block (callArgs ++ [.addi .a2 .s0 (d : Int), .li .a3 1])) encCall

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := dbl .s2 240 ldO ++ dbl .s0 ldO l0O

/-- `W + d ← pad(S)` (§4.1), `S` the `s5` bytes at `s4`
(`0 < s5 < 16`): zeros, the bytes copied, and `0x80` after them. -/
def padTo (d : Nat) : Prog isa :=
  .seq (.block (zero16 d ++ [.addi .a1 .s0 (d : Int), mov .a0 .s4, mov .a2 .s5]))
    (.seq copyLoop (.block [.li .t1 0x80, .store .b .t1 .a1 0]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`, for the `s5` bytes of nonce at `s4` and `tag_len` in `s8`:
zeros, the 1 in the byte before where the nonce goes, the nonce's bytes
copied to the end of the block, and `TAGLEN`'s bits in the top of the first
byte. Then `bottom` (its last 6 bits) to `W + botO`, and those bits
cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero16 tmpO ++ [.addi .a1 .s0 ((tmpO + 15 : Nat) : Int), .sub .a1 .a1 .s5, .li .t1 1,
      .store .b .t1 .a1 0, .addi .a1 .a1 1, mov .a0 .s4, mov .a2 .s5]))
    (.seq copyLoop
      (.block [.logicImm .and .t1 .s8 15, .shift .sll .d .t1 .t1 4, .load .b .t2 .s0 tmpO,
        .logic .or .t2 .t2 .t1, .store .b .t2 .s0 tmpO, .load .b .t2 .s0 (tmpO + 15),
        .logicImm .and .t1 .t2 63, .store .d .t1 .s0 botO, .logicImm .and .t2 .t2 0xc0,
        .store .b .t2 .s0 (tmpO + 15)]))

/-- `t5 := 0 − bit k of bottom` (in `t4`): all ones if it is set. -/
def stageMask (k : Nat) : List Instr :=
  (if k = 0 then [.logicImm .and .t5 .t4 1] else [.shift .srl .d .t5 .t4 k, .logicImm .and .t5 .t5 1]) ++
    ([.li .t6 0, .sub .t5 .t6 .t5] : List Instr)

/-- `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, `x'` in `t6`: `x'` if the mask (in `t5`) is
all ones, `x` if it is zero. -/
def sel (x : Reg) : List Instr := [.logic .xor .t6 .t6 x, .logic .and .t6 .t6 .t5, .logic .xor x x .t6]

/-- One stage of the shift of `Stretch` (in `t1`–`t3`, high to low): shifted
left by `a` (from 1 to 32) bits if bit `k` of `bottom` (in `t4`) is set, a
doubleword at a time from the high one, `x' = (x ⋘ a) ∨ (next ⋙ (64 − a))`. -/
def stage (k a : Nat) : List Instr :=
  stageMask k ++
  ([(Reg.t1, Reg.t2), (.t2, .t3)].flatMap fun (x, y) =>
    ([.shift .sll .d .t6 x a, .shift .srl .d .a6 y (64 - a), .logic .or .t6 .t6 .a6] : List Instr) ++ sel x) ++
  ([.shift .sll .d .t6 .t3 a] : List Instr) ++ sel .t3

/-- `Offset_0` from `Ktop` at `W + tmpO` and `bottom` at `W + botO`, to
`W + ofsO` and `W + o0O`: `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`
in `t1`–`t3`, shifted left by `bottom`, of which the high 128 bits. -/
def offset0 : List Instr :=
  loadBE64 .t1 .t0 .s0 tmpO ++ loadBE64 .t2 .t0 .s0 (tmpO + 8) ++
  ([.shift .sll .d .t3 .t1 8, .shift .srl .d .t6 .t2 56, .logic .or .t3 .t3 .t6, .logic .xor .t3 .t3 .t1,
   .load .d .t4 .s0 botO] : List Instr) ++
  stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage 5 32 ++
  storeBE 8 .t1 .t0 .s0 ofsO ++ storeBE 8 .t2 .t0 .s0 (ofsO + 8) ++
  storeBE 8 .t1 .t0 .s0 o0O ++ storeBE 8 .t2 .t0 .s0 (o0O + 8)

/-- `Offset_0`, for the `s5` bytes of nonce at `s4`. -/
def nonce : Prog isa := .seq nonceBlock (.seq (encOne tmpO) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `s4`) copied to `a7` (from
`W + bufO`, counting up, while `s5` counts down) and XORed with its offset,
`i` in `s6`. -/
def hashFill : Prog isa :=
  .seq lNtz
  (.seq (.block (xorW lO ohO ++ [mov .a0 .s4, mov .a1 .a7, .li .a2 16]))
  (.seq copyLoop
    (.block (xorB .a7 .s0 .a7 0 ohO 0 ++
      [.addi .a7 .a7 16, .addi .s4 .s4 16, .addi .s6 .s6 1, .addi .s5 .s5 (-1)]))))

/-- Add the blocks at `W + bufO` to the sum, `s5` of them (counting down,
with `a7` from `W + bufO`). -/
def hashSum : Prog isa :=
  .loop (.block (xorB .s0 .a7 .s0 sumO 0 sumO ++ [.addi .a7 .a7 16, .addi .s5 .s5 (-1)])) (.nonzero .s5)

/-- A chunk of `min(8, left)` blocks, `left` the blocks left (at
`W + hlO`; the chunk's at `W + cnO`): fill, encipher, add; `t1` the blocks
left after it. -/
def hashChunk : Prog isa :=
  .seq (.block [.load .d .t1 .s0 hlO, .shift .srl .d .t2 .t1 3])
  (.seq (.ite (.zero .t2) (.block [mov .s5 .t1]) (.block [.li .s5 8]))
  (.seq (.block [.store .d .s5 .s0 cnO, .load .d .t1 .s0 hlO, .sub .t1 .t1 .s5, .store .d .t1 .s0 hlO,
      .addi .a7 .s0 (bufO : Int)])
  (.seq (.loop hashFill (.nonzero .s5))
  (.seq (.block (callArgs ++ [.addi .a2 .s0 (bufO : Int), .load .d .a3 .s0 cnO]))
  (.seq encCall
  (.seq (.block [.addi .a7 .s0 (bufO : Int), .load .d .s5 .s0 cnO])
  (.seq hashSum (.block [.load .d .t1 .s0 hlO]))))))))

/-- The rest of the associated data (`s5` bytes at `s4`), padded, XORed
with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (xorB .s0 .s2 .s0 ohO 240 ohO))
    (.seq (padTo bufO)
      (.seq (.block (xorW ohO bufO))
        (.seq (encOne bufO) (.block (xorW bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`, with `aad` in its slot and `aad_len` in
`s10`. -/
def hash : Prog isa :=
  .seq (.block (zero16 sumO ++ zero16 ohO ++
      ([.load .d .s4 .s0 aadO, .shift .srl .d .t1 .s10 4, .store .d .t1 .s0 hlO, .li .s6 1] : List Instr)))
    (.seq (.ite (.zero .t1) (.block []) (.loop hashChunk (.nonzero .t1)))
      (.seq (.block [.logicImm .and .s5 .s10 15])
        (.ite (.zero .s5) (.block []) hashRest)))

/-! ## The whole blocks -/

/-- The offset of block `i` (in `s6`): `Offset ← Offset ⊕ L_{ntz(i)}`. -/
def nextOffset : Prog isa := .seq lNtz (.block (xorW lO ofsO))

/-- `W + ckO ⊕= (s4)`: the block copied to `W + t2O`, then added. -/
def addCk : Prog isa :=
  .seq (.block [mov .a0 .s4, .addi .a1 .s0 (t2O : Int), .li .a2 16]) (.seq copyLoop (.block (xorW t2O ckO)))

/-- `(s4) ⊕= W + ofsO`, a byte at a time. -/
def xorOfs : Prog isa := .seq (.block [.addi .a0 .s0 (ofsO : Int), mov .a1 .s4, .li .a2 16]) xorLoop

/-- On to the next block (`s5` is zero when none are left). -/
def nextBlock : List Instr := [.addi .s4 .s4 16, .addi .s6 .s6 1, .addi .s5 .s5 (-1)]

/-- A pass over the `s5` whole blocks of the data at `s4` (`s5 > 0`),
with `i` from 1 in `s6`: each block through `body` after its offset. -/
def pass (body : Prog isa) : Prog isa :=
  .loop (.seq nextOffset (.seq body (.block nextBlock))) (.nonzero .s5)

/-- The start of a pass over the whole blocks of the data (`len >> 4` of
them, at `data`). -/
def passStart : List Instr := [.load .d .s4 .s0 dataO, .shift .srl .d .s5 .s11 4, .li .s6 1]

/-- The whole blocks: `pre` (the first pass), `f` on all of them, `post` (the
third pass, the offsets recomputed from `Offset_0`). -/
def whole (f pre post : Prog isa) : Prog isa :=
  .seq (.block passStart)
    (.seq (pass pre)
      (.seq (.block (callArgs ++ ([.load .d .a2 .s0 dataO, .shift .srl .d .a3 .s11 4] : List Instr)))
        (.seq f
          (.seq (.block (copy16 o0O ofsO ++ passStart))
            (pass post)))))

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `s5` bytes at `s4`
(`0 < s5 < 16`), and add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O) (.block (xorW t2O ckO))

/-- The `s5` bytes at `s4` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa := .seq (.block [.addi .a0 .s0 (tmpO : Int), mov .a1 .s4, mov .a2 .s5]) xorLoop

/-- The rest of the data (`s5` bytes at `s4`, `s5 > 0`): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the
checksum of the plaintext, then the XOR; for `open`, the XOR, then the
checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (xorB .s0 .s2 .s0 ofsO 240 ofsO ++ copy16 ofsO tmpO))
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
  .seq (.block [.shift .srl .d .t1 .s11 4])
    (.seq (.ite (.zero .t1) (.block [])
        (if enc then whole encCall (.seq addCk xorOfs) xorOfs else whole decCall xorOfs (.seq xorOfs addCk)))
      (.seq (.block [.logicImm .and .s5 .s11 15, .sub .s4 .s11 .s5, .load .d .t1 .s0 dataO,
          .add .s4 .s4 .t1])
        (.ite (.zero .s5) (.block []) (rest enc))))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`: the entry,
`Offset_0`, `HASH`, the data and the tag. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq (.block entry) (.seq nonce (.seq hash (.seq (body enc) (tag d))))

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [mov .a0 .s0, mov .a1 .s9, mov .a2 .s8]) copyLoop

def «seal» : Prog isa := .seq (front true tagO) (.seq tagOut (.block restore))

/-- The received tag, the `tag_len` bytes at `tag`, padded with zeros at `W`. -/
def recv : Prog isa :=
  .seq (.block (zero16 tagO ++ ([mov .a0 .s9, mov .a1 .s0, mov .a2 .s8] : List Instr))) copyLoop

/-- `a0 = 1` if the padded tags at `W` and `W + vO` are equal, 0 if not,
without a branch (`1 − (0 <ᵤ x)` of the OR `x` of the XORs of their
doublewords). -/
def cmpTail : List Instr :=
  [.load .d .t1 .s0 tagO, .load .d .t2 .s0 vO, .logic .xor .t1 .t1 .t2, .load .d .t2 .s0 (tagO + 8),
   .load .d .t3 .s0 (vO + 8), .logic .xor .t2 .t2 .t3, .logic .or .t1 .t1 .t2, .li .t2 0,
   .sltu .t1 .t2 .t1, .li .a0 1, .sub .a0 .a0 .t1]

/-- The first `tag_len` bytes of the tag at `W + t2O`, padded with zeros at
`W + vO`, compared with the received one: `a0 = 1` if they are equal. -/
def cmp : Prog isa :=
  .seq (.block (zero16 vO ++ [.addi .a0 .s0 (t2O : Int), .addi .a1 .s0 (vO : Int), mov .a2 .s8]))
    (.seq copyLoop (.block cmpTail))

/-- Every byte of the data ANDed with `0 − a0`. -/
def mask : Prog isa :=
  .seq (.block [.load .d .s4 .s0 dataO, mov .s5 .s11, .li .t2 0, .sub .t5 .t2 .a0])
    (.ite (.zero .s5) (.block [])
      (.loop (.block [.load .b .t2 .s4 0, .logic .and .t2 .t2 .t5, .store .b .t2 .s4 0, .addi .s4 .s4 1,
        .addi .s5 .s5 (-1)]) (.nonzero .s5)))

def «open» : Prog isa :=
  .seq (front false t2O) (.seq recv (.seq cmp (.seq mask (.block restore))))

end VG.Impl.AesOcb.RISCV64
