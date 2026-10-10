import VerifiedGarbage.Impl.Aes.Arm.Blocks
import VerifiedGarbage.Impl.AesGcm.Arm

/-!
# AES-OCB: 32-bit ARM implementation

`vg_aes_ocb_seal(ctx = r0, rounds = r1, nonce = r2, nonce_len = r3,
aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12],
tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])` and
`vg_aes_ocb_open` with the same arguments (`Spec/Ocb/Contract.lean`), with
the working space (`work`) as a last argument, which a frame on the stack
allocates (`Impl.StackScratch.Arm.withStackScratch`), composed of calls of
the verified `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`, as on
AArch64 (`Impl/AesOcb/AArch64.lean`):

* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
* `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times, computed for each block by
  a loop on the public `i`; `L_$` and `L_0` are `L_*` doubled once and
  twice.
* `HASH(K, A)` copies up to 16 blocks of the associated data at a time,
  each XORed with its offset, to `W + bufO`, and enciphers them there.
* `Offset_0` takes the bits `bottom … bottom + 127` of `Stretch` (§4.2),
  where `bottom` is the last 6 bits of the nonce, which is secret: the
  192-bit `Stretch`, in six registers, is shifted left by 1, 2, 4, 8, 16
  and 32 bits, each shift kept or not by a mask from a bit of `bottom`.
* `seal` computes the tag at `W` and copies its first `tag_len` bytes to
  `tag` (`tagOut`).
* `open` copies the received tag, padded with zeros, to `W` (`recv`), and
  the first `tag_len` bytes of the tag it computes, padded with zeros, to
  `W + vO`, compares them without a branch (`cmp`) and ANDs every byte of
  the data with `0 − ok` (`mask`).

The key setup, `vg_aes_ocb_init`, is `vg_aes_gcm_init`'s
(`Impl.AesGcm.Arm.init`): a key context of AES-OCB is one of AES-GCM.

`vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks` take their working
space on the stack, which a frame pushes around each call (`push {r12, lr}`,
the working space in `r12`, as `Impl.AesGcm.Arm.ghFrame`): the functions use
8 bytes of stack.

## The working space `W` (`work`, 2560 bytes)

`[0, 16)`: the tag (out of `seal`; the received one, for `open`); then the
offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the current
`L_{ntz(i)}` and a block for one call, to 128; our caller's `r4`–`r11` and
our return address `lr` at `[128, 164)` (as AES-GCM saves them); the tag
`open` computes, the offset of `HASH`, `bottom`, the number of blocks of a
chunk of `HASH` and `Offset_0`, to 240; `[240, 256)`: the tag `open`
computes, padded; `[256, 512)`: 16 blocks of the associated data;
`[512, 2560)`: the working space of the functions called.

## Registers

`r11` holds `W`, `r10` the key context and `r9` the number of rounds
throughout; the functions called preserve them, and `r4`–`r8`, which hold
pointers and counts across calls: `r4` the data (or associated data)
pointer, `r5` a count of blocks or bytes, `r6` the block index `i`, `r7` the
number of whole blocks (of the data, or those of the associated data left),
`r8` the data or the buffer pointer of `HASH`. The other stack arguments are
read when they are needed (the stack pointer is the one on entry outside the
frames). `r0`–`r3`, `r12` and `lr` are temporaries.

The model has no register-offset addressing and branches only on `Z`: the
bytes are copied and XORed through advancing pointers, counting down with
`subs`. Only the pointers, the lengths, `rounds` and `tag_len` (and for
`open`, whether the tag is right) affect timing.
-/

namespace VG.Impl.AesOcb.Arm

open VG.Arm
open VG.Impl.AesGcm.Arm (imm addI save restore copyLoop xorLoop zero16)

/-! ## The working space -/

def tagO : Nat := 0
def ofsO : Nat := 16
def ckO : Nat := 32
def sumO : Nat := 48
def ldO : Nat := 64
def l0O : Nat := 80
def lO : Nat := 96
def tmpO : Nat := 112
def t2O : Nat := 176
def ohO : Nat := 192
def botO : Nat := 208
def cnO : Nat := 212
def o0O : Nat := 224
def vO : Nat := 240
def bufO : Nat := 256
def scrO : Nat := 512

/-! ## Blocks -/

/-- `cb + cd ← (pb + pd) ⊕ (qb + qd)`, a word at a time through `r0` and
`r1`. -/
def xorB (pb qb cb : Reg) (pd qd cd : Nat) : List Instr :=
  [.ldr .r0 pb pd, .ldr .r1 qb qd, .dp .eor .r0 .r0 (.reg .r1), .str .r0 cb cd,
   .ldr .r0 pb (pd + 4), .ldr .r1 qb (qd + 4), .dp .eor .r0 .r0 (.reg .r1), .str .r0 cb (cd + 4),
   .ldr .r0 pb (pd + 8), .ldr .r1 qb (qd + 8), .dp .eor .r0 .r0 (.reg .r1), .str .r0 cb (cd + 8),
   .ldr .r0 pb (pd + 12), .ldr .r1 qb (qd + 12), .dp .eor .r0 .r0 (.reg .r1), .str .r0 cb (cd + 12)]

/-- `W + d ← W + d ⊕ W + s`. -/
def xorW (s d : Nat) : List Instr := xorB .r11 .r11 .r11 d s d

/-- `W + d ← W + s` (all loads first). -/
def copy16 (s d : Nat) : List Instr :=
  [.ldr .r0 .r11 s, .ldr .r1 .r11 (s + 4), .ldr .r2 .r11 (s + 8), .ldr .r3 .r11 (s + 12), .str .r0 .r11 d,
   .str .r1 .r11 (d + 4), .str .r2 .r11 (d + 8), .str .r3 .r11 (d + 12)]

/-- `W + d ← double(b + s)` (§2): the block is big-endian, so each word is
byte-reversed into `r0` (the most significant) to `r3`, shifted left by one
bit, the carry out of `r0` reducing `r3` by `{87}` through a mask
(`(c - 1) ∧ {87} ⊕ {87}` for the carry `c`), and byte-reversed back. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  [.ldr .r0 b s, .ldr .r1 b (s + 4), .ldr .r2 b (s + 8), .ldr .r3 b (s + 12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .mov .r12 (.shifted .r0 .lsr 31), .dp .sub .r12 .r12 (imm 1), .dp .and .r12 .r12 (imm 0x87),
   .dp .eor .r12 .r12 (imm 0x87),
   .mov .r0 (.shifted .r0 .lsl 1), .dp .orr .r0 .r0 (.shifted .r1 .lsr 31),
   .mov .r1 (.shifted .r1 .lsl 1), .dp .orr .r1 .r1 (.shifted .r2 .lsr 31),
   .mov .r2 (.shifted .r2 .lsl 1), .dp .orr .r2 .r2 (.shifted .r3 .lsr 31),
   .mov .r3 (.shifted .r3 .lsl 1), .dp .eor .r3 .r3 (.reg .r12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .str .r0 .r11 d, .str .r1 .r11 (d + 4), .str .r2 .r11 (d + 8), .str .r3 .r11 (d + 12)]

/-- `r12 := lr ∧ 1`, and `Z` set if it is zero. -/
def low1 : List Instr := [.dp .and .r12 .lr (imm 1), .cmp .r12 (imm 0)]

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `r6`: `L_0` doubled while the low
bit of `lr` (from `i`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ ([.mov .lr (.reg .r6)] : List Instr) ++ low1))
    (.ite .eq (.loop (.block (dbl .r11 lO lO ++ ([.mov .lr (.shifted .lr .lsr 1)] : List Instr) ++ low1)) .eq) (.block []))

/-! ## Calls -/

/-- `vg_aes_encrypt_blocks`, with the working space in `r12` pushed as its
stack argument. -/
def encFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_encrypt_blocks" Impl.Aes.Arm.encryptBlocks) (.pop .r12 8)

/-- `vg_aes_decrypt_blocks`, likewise. -/
def decFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_aes_decrypt_blocks" Impl.Aes.Arm.decryptBlocks) (.pop .r12 8)

/-- The arguments of a call but the blocks: the key context's schedule, the
number of rounds and the working space. -/
def callArgs : List Instr := [.mov .r0 (.reg .r10), .mov .r1 (.reg .r9), addI .r12 .r11 scrO]

/-- `ENCIPHER` of the block at `W + d`, in place. -/
def encOne (d : Nat) : Prog isa := .seq (.block (callArgs ++ [addI .r2 .r11 d, .mov .r3 (imm 1)])) encFrame

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := dbl .r10 240 ldO ++ dbl .r11 ldO l0O

/-- `W + d ← pad(S)` (§4.1), `S` the `r5` bytes at `r4` (`0 < r5 < 16`):
zeros, the bytes copied, and `0x80` after them. -/
def padTo (d : Nat) : Prog isa :=
  .seq (.block (zero16 d ++ [addI .r2 .r11 d, .mov .r1 (.reg .r4), .mov .r3 (.reg .r5)]))
    (.seq copyLoop (.block [.mov .r0 (imm 0x80), .strb .r0 .r2 0]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`, for the `r5` bytes of nonce at `r4` and `tag_len` at
`[sp + 20]`: zeros, the 1 in the byte before where the nonce goes, the
nonce's bytes copied to the end of the block, and `TAGLEN`'s bits in the
top of the first byte. Then `bottom` (its last 6 bits) to `W + botO`, and
those bits cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero16 tmpO ++ [addI .r2 .r11 (tmpO + 15), .dp .sub .r2 .r2 (.reg .r5), .mov .r0 (imm 1),
      .strb .r0 .r2 0, addI .r2 .r2 1, .mov .r1 (.reg .r4), .mov .r3 (.reg .r5)]))
    (.seq copyLoop
      (.block [.ldrSp .r0 20, .dp .and .r0 .r0 (imm 15), .mov .r0 (.shifted .r0 .lsl 4), .ldrb .r1 .r11 tmpO,
        .dp .orr .r1 .r1 (.reg .r0), .strb .r1 .r11 tmpO, .ldrb .r1 .r11 (tmpO + 15),
        .dp .and .r0 .r1 (imm 63), .str .r0 .r11 botO, .dp .and .r1 .r1 (imm 0xc0),
        .strb .r1 .r11 (tmpO + 15)]))

/-- `r7 := 0 − bit k of bottom` (in `r6`): all ones if it is set. -/
def stageMask (k : Nat) : List Instr :=
  (if k = 0 then [.dp .and .r7 .r6 (imm 1)] else [.mov .r7 (.shifted .r6 .lsr k), .dp .and .r7 .r7 (imm 1)]) ++
    ([.mov .r8 (imm 0), .dp .sub .r7 .r8 (.reg .r7)] : List Instr)

/-- `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, `x'` in `r8`: `x'` if the mask (in `r7`) is
all ones, `x` if it is zero. -/
def sel (x : Reg) : List Instr := [.dp .eor .r8 .r8 (.reg x), .dp .and .r8 .r8 (.reg .r7), .dp .eor x x (.reg .r8)]

/-- The words of `Stretch`, high to low. -/
def sw : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5]

/-- One stage of the shift of `Stretch` (in `r0`–`r5`, high to low): shifted
left by `a` (from 1 to 31) bits if bit `k` of `bottom` (in `r6`) is set, a
word at a time from the high one, `x' = (x ⋘ a) ∨ (next ⋙ (32 − a))`. -/
def stage (k a : Nat) : List Instr :=
  stageMask k ++
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    ([.mov .r8 (.shifted x .lsl a), .dp .orr .r8 .r8 (.shifted y .lsr (32 - a))] : List Instr) ++ sel x) ++
  ([.mov .r8 (.shifted .r5 .lsl a)] : List Instr) ++ sel .r5

/-- The last stage: shifted left by 32 bits (a word) if bit 5 of `bottom` is
set. -/
def stage32 : List Instr :=
  stageMask 5 ++
  ([(Reg.r0, Reg.r1), (.r1, .r2), (.r2, .r3), (.r3, .r4), (.r4, .r5)].flatMap fun (x, y) =>
    ([.mov .r8 (.reg y)] : List Instr) ++ sel x) ++
  ([.mov .r8 (imm 0)] : List Instr) ++ sel .r5

/-- `Offset_0` from `Ktop` at `W + tmpO` and `bottom` at `W + botO`, to
`W + ofsO` and `W + o0O`: `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`
in `r0`–`r5`, shifted left by `bottom`, of which the high 128 bits. -/
def offset0 : List Instr :=
  ([.ldr .r0 .r11 tmpO, .ldr .r1 .r11 (tmpO + 4), .ldr .r2 .r11 (tmpO + 8), .ldr .r3 .r11 (tmpO + 12),
   .rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .mov .r4 (.shifted .r0 .lsl 8), .dp .orr .r4 .r4 (.shifted .r1 .lsr 24), .dp .eor .r4 .r4 (.reg .r0),
   .mov .r5 (.shifted .r1 .lsl 8), .dp .orr .r5 .r5 (.shifted .r2 .lsr 24), .dp .eor .r5 .r5 (.reg .r1),
   .ldr .r6 .r11 botO] : List Instr) ++
  stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage32 ++
  ([.rev .r0 .r0, .rev .r1 .r1, .rev .r2 .r2, .rev .r3 .r3,
   .str .r0 .r11 ofsO, .str .r1 .r11 (ofsO + 4), .str .r2 .r11 (ofsO + 8), .str .r3 .r11 (ofsO + 12),
   .str .r0 .r11 o0O, .str .r1 .r11 (o0O + 4), .str .r2 .r11 (o0O + 8), .str .r3 .r11 (o0O + 12)] : List Instr)

/-- `Offset_0`, for the `r5` bytes of nonce at `r4`. -/
def nonce : Prog isa := .seq nonceBlock (.seq (encOne tmpO) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `r4`) XORed with its offset to
`r8` (from `W + bufO`, counting up, while `r5` counts down), `i` in `r6`. -/
def hashFill : Prog isa :=
  .seq lNtz
    (.block (xorW lO ohO ++ xorB .r4 .r11 .r8 0 ohO 0 ++
      [addI .r8 .r8 16, addI .r4 .r4 16, addI .r6 .r6 1, .subs .r5 .r5 (imm 1)]))

/-- Add the blocks at `W + bufO` to the sum, `r5` of them (counting down,
with `r8` from `W + bufO`). -/
def hashSum : Prog isa :=
  .loop (.block (xorB .r11 .r8 .r11 sumO 0 sumO ++ [addI .r8 .r8 16, .subs .r5 .r5 (imm 1)])) .ne

/-- A chunk of `min(16, r7)` blocks, `r7` the blocks left (also kept at
`W + cnO`): fill, encipher, add; `Z` set when no block is left. -/
def hashChunk : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r7 .lsr 4), .cmp .r12 (imm 0)])
  (.seq (.ite .eq (.block [.mov .r5 (.reg .r7)]) (.block [.mov .r5 (imm 16)]))
  (.seq (.block [.str .r5 .r11 cnO, .dp .sub .r7 .r7 (.reg .r5), addI .r8 .r11 bufO])
  (.seq (.loop hashFill .ne)
  (.seq (.block (callArgs ++ [addI .r2 .r11 bufO, .ldr .r3 .r11 cnO]))
  (.seq encFrame
  (.seq (.block [addI .r8 .r11 bufO, .ldr .r5 .r11 cnO])
  (.seq hashSum (.block [.cmp .r7 (imm 0)]))))))))

/-- The rest of the associated data (`r5` bytes at `r4`), padded, XORed
with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (xorB .r11 .r10 .r11 ohO 240 ohO))
    (.seq (padTo bufO)
      (.seq (.block (xorW ohO bufO))
        (.seq (encOne bufO) (.block (xorW bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` at `[sp]` and
`[sp + 4]`. -/
def hash : Prog isa :=
  .seq (.block (zero16 sumO ++ zero16 ohO ++
      ([.ldrSp .r4 0, .ldrSp .r7 4, .mov .r7 (.shifted .r7 .lsr 4), .mov .r6 (imm 1), .cmp .r7 (imm 0)] : List Instr)))
    (.seq (.ite .eq (.block []) (.loop hashChunk .ne))
      (.seq (.block [.ldrSp .r5 4, .dp .and .r5 .r5 (imm 15), .cmp .r5 (imm 0)])
        (.ite .eq (.block []) hashRest)))

/-! ## The whole blocks -/

/-- The offset of block `i` (in `r6`): `Offset ← Offset ⊕ L_{ntz(i)}`. -/
def nextOffset : Prog isa := .seq lNtz (.block (xorW lO ofsO))

/-- `W + ckO ⊕= (r4)`. -/
def addCk : List Instr := xorB .r11 .r4 .r11 ckO 0 ckO

/-- `(r4) ⊕= W + ofsO`. -/
def xorOfs : List Instr := xorB .r4 .r11 .r4 0 ofsO 0

/-- On to the next block (`r5` is zero when none are left). -/
def nextBlock : List Instr := [addI .r4 .r4 16, addI .r6 .r6 1, .subs .r5 .r5 (imm 1)]

/-- A pass over the `r5` whole blocks of the data at `r4` (`r5 > 0`), with
`i` from 1 in `r6`: each block through `body` after its offset. -/
def pass (body : List Instr) : Prog isa :=
  .loop (.seq nextOffset (.block (body ++ nextBlock))) .ne

/-- The start of a pass over the `r7` whole blocks of the data at `r8`. -/
def passStart : List Instr := [.mov .r4 (.reg .r8), .mov .r5 (.reg .r7), .mov .r6 (imm 1)]

/-- The whole blocks: `pre` (the first pass), `f` on all of them, `post` (the
third pass, the offsets recomputed from `Offset_0`); `r7` their number,
`r8` the data. -/
def whole (f : Prog isa) (pre post : List Instr) : Prog isa :=
  .seq (.block passStart)
    (.seq (pass pre)
      (.seq (.block (callArgs ++ ([.mov .r2 (.reg .r8), .mov .r3 (.reg .r7)] : List Instr)))
        (.seq f
          (.seq (.block (copy16 o0O ofsO ++ passStart))
            (pass post)))))

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `r5` bytes at `r4` (`0 < r5 < 16`), and
add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O) (.block (xorW t2O ckO))

/-- The `r5` bytes at `r4` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa :=
  .seq (.block [addI .r1 .r11 tmpO, .mov .r2 (.reg .r4), .mov .r3 (.reg .r5)]) xorLoop

/-- The rest of the data (`r5` bytes at `r4`, `r5 > 0`): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the
checksum of the plaintext, then the XOR; for `open`, the XOR, then the
checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (xorB .r11 .r10 .r11 ofsO 240 ofsO ++ copy16 ofsO tmpO))
    (.seq (encOne tmpO)
      (if enc then .seq padCk xorPad else .seq xorPad padCk))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to
`W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block (copy16 ckO tmpO ++ xorW ofsO tmpO ++ xorW ldO tmpO))
    (.seq (encOne tmpO)
      (.block (copy16 tmpO d ++ xorW sumO d)))

/-! ## The functions -/

/-- The entry: our caller's registers saved in `W`, the key context and the
number of rounds in `r10` and `r9`, the nonce and its length in `r4` and
`r5`, `L_$` and `L_0`, the checksum zeroed. -/
def entry : List Instr :=
  .ldrSp .r12 24 :: save .r12 ++
    ([.mov .r11 (.reg .r12), .mov .r10 (.reg .r0), .mov .r9 (.reg .r1), .mov .r4 (.reg .r2), .mov .r5 (.reg .r3)] : List Instr) ++
    lsetup ++ zero16 ckO

/-- The data: whole blocks, then the rest. -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [.ldrSp .r8 8, .ldrSp .r7 12, .mov .r7 (.shifted .r7 .lsr 4), .cmp .r7 (imm 0)])
    (.seq (.ite .eq (.block [])
        (if enc then whole encFrame (addCk ++ xorOfs) xorOfs else whole decFrame xorOfs (xorOfs ++ addCk)))
      (.seq (.block [.ldrSp .r5 12, .dp .and .r5 .r5 (imm 15), .ldrSp .r4 12, .dp .sub .r4 .r4 (.reg .r5),
          .dp .add .r4 .r4 (.reg .r8), .cmp .r5 (imm 0)])
        (.ite .eq (.block []) (rest enc))))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`: the entry,
`Offset_0`, `HASH`, the data and the tag. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq (.block entry) (.seq nonce (.seq hash (.seq (body enc) (tag d))))

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [.ldrSp .r2 16, .mov .r1 (.reg .r11), .ldrSp .r3 20]) copyLoop

def «seal» : Prog isa := .seq (front true tagO) (.seq tagOut (.block restore))

/-- The received tag, the `tag_len` bytes at `tag`, padded with zeros at `W`. -/
def recv : Prog isa :=
  .seq (.block (zero16 tagO ++ ([.ldrSp .r1 16, .mov .r2 (.reg .r11), .ldrSp .r3 20] : List Instr))) copyLoop

/-- Word `k` of the XOR of the two padded tags into `d`. -/
def xorT (d : Reg) (k : Nat) : List Instr :=
  [.ldr d .r11 (tagO + 4 * k), .ldr .r2 .r11 (vO + 4 * k), .dp .eor d d (.reg .r2)]

/-- `r0 = 1` if the padded tags at `W` and `W + vO` are equal, 0 if not,
without a branch (`1 - ((x | -x) >> 31)` of the OR `x` of the XORs of their
words). -/
def cmpTail : List Instr :=
  xorT .r0 0 ++ xorT .r1 1 ++ ([.dp .orr .r0 .r0 (.reg .r1)] : List Instr) ++ xorT .r1 2 ++
    ([.dp .orr .r0 .r0 (.reg .r1)] : List Instr) ++ xorT .r1 3 ++
    ([.dp .orr .r0 .r0 (.reg .r1), .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0),
     .dp .orr .r0 .r0 (.reg .r1), .mov .r0 (.shifted .r0 .lsr 31), .mov .r1 (imm 1),
     .dp .sub .r0 .r1 (.reg .r0)] : List Instr)

/-- The first `tag_len` bytes of the tag at `W + t2O`, padded with zeros at
`W + vO`, compared with the received one: `r0 = 1` if they are equal. -/
def cmp : Prog isa :=
  .seq (.block (zero16 vO ++ [addI .r1 .r11 t2O, addI .r2 .r11 vO, .ldrSp .r3 20]))
    (.seq copyLoop (.block cmpTail))

/-- Every byte of the data ANDed with `0 − r0`. -/
def mask : Prog isa :=
  .seq (.block [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r0), .cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1,
        .subs .r5 .r5 (imm 1)]) .ne))

def «open» : Prog isa :=
  .seq (front false t2O) (.seq recv (.seq cmp (.seq mask (.block restore))))

end VG.Impl.AesOcb.Arm
