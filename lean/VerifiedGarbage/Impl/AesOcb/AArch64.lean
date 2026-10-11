module

public import VerifiedGarbage.Impl.Aes.AArch64.Callee
public import VerifiedGarbage.Impl.AesGcm.AArch64

/-!
# AES-OCB: AArch64 implementation

`vg_aes_ocb_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`,
`vg_aes_ocb_seal(ctx = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7, tag = [sp], tag_len = [sp + 8], work = [sp + 16])`
and `vg_aes_ocb_open` with the same arguments (`Spec/Ocb/Contract.lean`),
with the working space (`scratch`, `work`) as a last argument, which a frame
on the stack allocates (`Impl.StackScratch.AArch64.withStackScratch` and
`withStackArgScratch`), composed of calls of the verified
`vg_aes_expand_key_scratch`, `vg_aes_encrypt_blocks` and `vg_aes_decrypt_blocks`,
and generic over their implementations (`Callees`): each function is
emitted once for each. As the x86-64 implementation (`X86_64.lean`):

* `init` expands the key into the key context and enciphers a zero block in
  place, at byte 240, for `L_*`.
* The whole blocks of the data are processed in three passes over the data,
  in place: XOR each block with its offset `Offset_i` (and, for `seal`, add
  it to the checksum), encipher or decipher all of them in one call, then
  XOR each with its offset again (and, for `open`, add it to the
  checksum). The offsets are recomputed in the third pass, from `Offset_0`.
* `L_{ntz(i)}` is `L_0` doubled `ntz(i)` times, computed for each block by
  a loop on the public `i`; `L_$` and `L_0` are `L_*` doubled once and
  twice.
* `HASH(K, A)` copies up to 8 blocks of the associated data at a time,
  each XORed with its offset, to `W + bufO`, and enciphers them there.
* `Offset_0` takes the bits `bottom … bottom + 127` of `Stretch` (§4.2),
  where `bottom` is the last 6 bits of the nonce, which is secret: the
  192-bit `Stretch`, in three registers, is shifted left by 1, 2, 4, 8, 16
  and 32 bits, each shift kept or not by a mask from a bit of `bottom`.
* `seal` computes the tag at `W` (`front`) and copies its first `tag_len`
  bytes to `tag`, whose address it reads from the stack (`tagOut`).
* `open` copies the received tag from `tag` to `W` (`recv`), compares the
  tags without a branch and masks the data with `0 − ok`.

The model has no flags or register-offset addressing: the branches are
`cbz`/`cbnz` on counts, and bytes are copied and XORed through advancing
pointers (`Impl.AesGcm.AArch64.copyLoop` and `xorLoop`).

## The working space `W` (`work`, 2560 bytes)

`[0, 16)`: the tag (out of `seal`; the received one, for `open`); then the
offset, the checksum, the sum of `HASH`, `L_$`, `L_0`, the current
`L_{ntz(i)}`, a block for one call, the computed tag of `open` and the
offset of `HASH`, to 160; our caller's `x19`–`x28` and our return address
`x30` at `[160, 248)`; the public arguments kept in memory, `tag_len`,
`aad`, `aad_len`, `nonce` and `nonce_len`, at `[248, 288)`, which nothing
writes after the entry; `bottom` and `Offset_0` at `[288, 320)`;
`[384, 512)`: 8 blocks of the associated data; `[512, 2560)`: the working
space of the functions called. A call (`bl`) stores nothing in memory, so
no stack is used.

## Registers

`x19` holds `W`, `x20` the key context, `x21` the data, `x22` the number of
rounds and `x28` the data's length throughout; the functions called
preserve them, and `x23`–`x27`, which hold pointers and counts across calls:
`x23` the data (or associated data) pointer, `x24` a count of blocks or
bytes, `x25` the block index `i`, `x26` the number of whole blocks (of the
data, or those of the associated data left), `x27` the buffer pointer of
`HASH`; `x15` counts the blocks of a chunk of `HASH`. Only the pointers, the
lengths, `rounds` and `tag_len` (and for `open`, whether the tag is right)
affect timing.
-/

@[expose] public section

namespace VG.Impl.AesOcb.AArch64

open VG.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm copyLoop xorLoop)

/-- The implementations called: AES's encryption and decryption of whole
blocks and its key expansion. -/
structure Callees where
  enc : Impl.Aes.AArch64.Blocks
  dec : Impl.Aes.AArch64.Blocks
  key : Impl.Aes.AArch64.ExpandKey

def ld (r b : Reg) (d : Nat) : Instr := .ldr .x r b d
def st (b : Reg) (d : Nat) (r : Reg) : Instr := .str .x r b d

/-! ## The working space -/

def tagO : Nat := 0
def ofsO : Nat := 16
def ckO : Nat := 32
def sumO : Nat := 48
def ldO : Nat := 64
def l0O : Nat := 80
def lO : Nat := 96
def tmpO : Nat := 112
def t2O : Nat := 128
def ohO : Nat := 144
def savO : Nat := 160
def tlO : Nat := 248
def aadO : Nat := 256
def alenO : Nat := 264
def nO : Nat := 272
def nlO : Nat := 280
def botO : Nat := 288
def o0O : Nat := 304
def bufO : Nat := 384
def scrO : Nat := 512

/-- Our caller's registers and our return address, and where they are kept,
`x19` (the base of the restore) last. -/
def saved : List (Reg × Nat) :=
  [(.x20, savO + 8), (.x21, savO + 16), (.x22, savO + 24), (.x23, savO + 32), (.x24, savO + 40),
   (.x25, savO + 48), (.x26, savO + 56), (.x27, savO + 64), (.x28, savO + 72), (.x30, savO + 80),
   (.x19, savO)]

def save (b : Reg) : List Instr := saved.map fun (r, d) => st b d r
def restore : List Instr := saved.map fun (r, d) => ld r .x19 d

/-! ## Blocks of `W` -/

/-- `W + d ← 0` (16 bytes). -/
def zero16 (d : Nat) : List Instr := [imm .x9 0, st .x19 d .x9, st .x19 (d + 8) .x9]

/-- `W + d ← W + s`. -/
def copy16 (s d : Nat) : List Instr :=
  [ld .x9 .x19 s, ld .x10 .x19 (s + 8), st .x19 d .x9, st .x19 (d + 8) .x10]

/-- `W + d ← W + d ⊕ (b + s)`. -/
def xor16 (b : Reg) (s d : Nat) : List Instr :=
  [ld .x9 .x19 d, ld .x10 .x19 (d + 8), ld .x11 b s, ld .x12 b (s + 8),
   .logic .eor .x .x9 .x9 .x11, .logic .eor .x .x10 .x10 .x12, st .x19 d .x9, st .x19 (d + 8) .x10]

/-- `W + d ← double(b + s)` (§2): the block is big-endian, so each half is
byte-reversed into `x9` (high) and `x10` (low), shifted left by one bit, the
carry out of the high half reducing the low one by `{87}` through a mask,
and byte-reversed back. -/
def dbl (b : Reg) (s d : Nat) : List Instr :=
  [ld .x9 b s, .rev .x9 .x9, ld .x10 b (s + 8), .rev .x10 .x10,
   .lsr .x .x11 .x9 63, imm .x12 0, .sub .x .x12 .x12 .x11, imm .x13 0x87,
   .logic .and .x .x12 .x12 .x13,
   .lsr .x .x11 .x10 63, .lsl .x .x9 .x9 1, .logic .orr .x .x9 .x9 .x11,
   .lsl .x .x10 .x10 1, .logic .eor .x .x10 .x10 .x12,
   .rev .x9 .x9, st .x19 d .x9, .rev .x10 .x10, st .x19 (d + 8) .x10]

/-- `x12 := x14 ∧ 1`. -/
def low1 : List Instr := [imm .x12 1, .logic .and .x .x12 .x14 .x12]

/-- `W + lO ← L_{ntz(i)}` for `i ≥ 1` in `x25`: `L_0` doubled while the low
bit of `x14` (from `i`, shifted right each time) is zero. -/
def lNtz : Prog isa :=
  .seq (.block (copy16 l0O lO ++ [mov .x14 .x25] ++ low1))
    (.ite (.zero .x .x12) (.loop (.block (dbl .x19 lO lO ++ ([.lsr .x .x14 .x14 1] : List Instr) ++ low1)) (.zero .x .x12))
      (.block []))

/-! ## Calls -/

/-- `ENCIPHER` (`c.enc`) or `DECIPHER` (`c.dec`) of the `x3` blocks at `x2`
(set up by `args`), with the key context's schedule and the working space
at `W + scrO`. -/
def callBlocks (f : Impl.Aes.AArch64.Blocks) (args : List Instr) : Prog isa :=
  .seq (.block (args ++ [mov .x0 .x20, mov .x1 .x22, ptr .x4 .x19 scrO])) (.call f.name f.code)

/-- One block of `W`, at `W + d`. -/
def oneBlock (d : Nat) : List Instr := [ptr .x2 .x19 d, imm .x3 1]

/-! ## `L_$`, `L_0` and `Offset_0` -/

/-- `L_$` and `L_0` from `L_*` (bytes 240–255 of the key context). -/
def lsetup : List Instr := dbl .x20 240 ldO ++ dbl .x19 ldO l0O

/-- `W + d ← pad(S)` (§4.1), `S` the `x24` bytes at `x23` (`0 < x24 < 16`):
zeros, the bytes copied, and `0x80` after them. -/
def padTo (d : Nat) : Prog isa :=
  .seq (.block (zero16 d ++ [ptr .x11 .x19 d, mov .x12 .x23, mov .x13 .x24]))
    (.seq copyLoop (.block [imm .x9 0x80, .strb .x9 .x11 0]))

/-- The nonce block (§4.2), `num2str(TAGLEN mod 128, 7) ‖ zeros ‖ 1 ‖ N`, at
`W + tmpO`, with `nonce`, `nonce_len` and `tag_len` in `W + nO`, `W + nlO`
and `W + tlO`: zeros, the 1 in the byte before where the nonce goes, the
nonce's bytes copied to the end of the block, and `TAGLEN`'s bits in the
top of the first byte. Then `bottom` (its last 6 bits) to `W + botO`, and
those bits cleared. -/
def nonceBlock : Prog isa :=
  .seq (.block (zero16 tmpO ++ [ld .x12 .x19 nO, ld .x13 .x19 nlO]))
    (.seq (.block [ptr .x11 .x19 (tmpO + 16), .sub .x .x11 .x11 .x13, .subImm .x .x14 .x11 1, imm .x9 1,
      .strb .x9 .x14 0])
    (.seq copyLoop
      (.block [ld .x10 .x19 tlO, imm .x11 15, .logic .and .x .x10 .x10 .x11, .lsl .x .x10 .x10 4,
        .ldrb .x9 .x19 tmpO, .logic .orr .x .x9 .x9 .x10, .strb .x9 .x19 tmpO,
        .ldrb .x9 .x19 (tmpO + 15), imm .x11 63, .logic .and .x .x10 .x9 .x11, st .x19 botO .x10,
        imm .x11 0xc0, .logic .and .x .x9 .x9 .x11, .strb .x9 .x19 (tmpO + 15)])))

/-- One stage of the shift of `Stretch` (in `x9`, `x10`, `x11`, high to
low): shifted left by `a` bits if bit `k` of `bottom` (in `x12`) is set.
`x13`–`x15` are temporaries. -/
def stage (k a : Nat) : List Instr :=
  -- The mask: all ones if bit `k` is set.
  ([.lsr .x .x13 .x12 k, imm .x14 1, .logic .and .x .x13 .x13 .x14, imm .x14 0,
   .sub .x .x13 .x14 .x13] : List Instr) ++
  -- Each word, from the high one: `x ← x ⊕ ((x' ⊕ x) ∧ mask)`, where
  -- `x' = (x ⋘ a) ∨ (next ⋙ (64 − a))`.
  ([(Reg.x9, Reg.x10), (.x10, .x11)].flatMap fun (x, y) =>
    [.lsl .x .x14 x a, .lsr .x .x15 y (64 - a), .logic .orr .x .x14 .x14 .x15,
     .logic .eor .x .x14 .x14 x, .logic .and .x .x14 .x14 .x13, .logic .eor .x x x .x14]) ++
  ([.lsl .x .x14 .x11 a, .logic .eor .x .x14 .x14 .x11, .logic .and .x .x14 .x14 .x13,
   .logic .eor .x .x11 .x11 .x14] : List Instr)

/-- `Offset_0` from `Ktop` at `W + tmpO` and `bottom` at `W + botO`, to
`W + ofsO` and `W + o0O`: `Stretch = Ktop ‖ (Ktop[1..64] ⊕ Ktop[9..72])`
in `x9`, `x10`, `x11`, shifted left by `bottom`, of which the high 128
bits. -/
def offset0 : List Instr :=
  [ld .x9 .x19 tmpO, .rev .x9 .x9, ld .x10 .x19 (tmpO + 8), .rev .x10 .x10,
   .lsl .x .x11 .x9 8, .lsr .x .x13 .x10 56, .logic .orr .x .x11 .x11 .x13,
   .logic .eor .x .x11 .x11 .x9, ld .x12 .x19 botO] ++
  stage 0 1 ++ stage 1 2 ++ stage 2 4 ++ stage 3 8 ++ stage 4 16 ++ stage 5 32 ++
  ([.rev .x9 .x9, .rev .x10 .x10, st .x19 ofsO .x9, st .x19 (ofsO + 8) .x10, st .x19 o0O .x9,
   st .x19 (o0O + 8) .x10] : List Instr)

variable (c : Callees)

/-- `Offset_0`. -/
def nonce : Prog isa :=
  .seq nonceBlock (.seq (callBlocks c.enc (oneBlock tmpO)) (.block offset0))

/-! ## `HASH` -/

/-- One block of the associated data (at `x23`) XORed with its offset to
`x27` (from `W + bufO`, counting up, while `x15` counts down), `i` in
`x25`. -/
def hashFill : Prog isa :=
  .seq lNtz
    (.block (xor16 .x19 lO ohO ++
      [ld .x9 .x23 0, ld .x10 .x23 8, ld .x11 .x19 ohO, ld .x12 .x19 (ohO + 8),
       .logic .eor .x .x9 .x9 .x11, .logic .eor .x .x10 .x10 .x12, st .x27 0 .x9, st .x27 8 .x10,
       ptr .x27 .x27 16, ptr .x23 .x23 16, ptr .x25 .x25 1, .subImm .x .x15 .x15 1]))

/-- `x27 ← W + bufO`, `x15 ← x24`. -/
def bufStart : List Instr := [ptr .x27 .x19 bufO, mov .x15 .x24]

/-- Add the `x24` blocks at `W + bufO` to the sum. -/
def hashSum : Prog isa :=
  .seq (.block bufStart)
    (.loop (.block (xor16 .x27 0 sumO ++ [ptr .x27 .x27 16, .subImm .x .x15 .x15 1]))
      (.nonzero .x .x15))

/-- A chunk of `x24 = min(8, x26)` blocks, `x26` the blocks left: fill,
encipher, add; then on to the next (`x26` is zero when none are left). -/
def hashChunk : Prog isa :=
  .seq (.block [.subImm .x .x9 .x26 8, .lsr .x .x9 .x9 63, mov .x24 .x26])
    (.seq (.ite (.zero .x .x9) (.block [imm .x24 8]) (.block []))
      (.seq (.block bufStart)
        (.seq (.loop hashFill (.nonzero .x .x15))
          (.seq (callBlocks c.enc [ptr .x2 .x19 bufO, mov .x3 .x24])
            (.seq hashSum (.block [.sub .x .x26 .x26 .x24]))))))

/-- The rest of the associated data (`x24` bytes at `x23`), padded, XORed
with the offset `⊕ L_*`, enciphered and added to the sum. -/
def hashRest : Prog isa :=
  .seq (.block (xor16 .x20 240 ohO))
    (.seq (padTo bufO)
      (.seq (.block (xor16 .x19 ohO bufO))
        (.seq (callBlocks c.enc (oneBlock bufO)) (.block (xor16 .x19 bufO sumO)))))

/-- `HASH(K, A)` to `W + sumO`, with `aad` and `aad_len` in `W + aadO` and
`W + alenO`. -/
def hash : Prog isa :=
  .seq (.block (zero16 sumO ++ zero16 ohO ++ [ld .x23 .x19 aadO, ld .x26 .x19 alenO]))
    (.seq (.block [.lsr .x .x26 .x26 4, imm .x25 1])
      (.seq (.ite (.zero .x .x26) (.block []) (.loop (hashChunk c) (.nonzero .x .x26)))
        (.seq (.block [ld .x24 .x19 alenO, imm .x10 15, .logic .and .x .x24 .x24 .x10])
          (.ite (.zero .x .x24) (.block []) (hashRest c)))))

/-! ## The whole blocks -/

/-- The offset of block `i` (in `x25`): `Offset ← Offset ⊕ L_{ntz(i)}`. -/
def nextOffset : Prog isa := .seq lNtz (.block (xor16 .x19 lO ofsO))

/-- `W + ckO ⊕= (x23)`. -/
def addCk : List Instr := xor16 .x23 0 ckO

/-- `(x23) ⊕= W + ofsO`. -/
def xorOfs : List Instr :=
  [ld .x9 .x23 0, ld .x10 .x23 8, ld .x11 .x19 ofsO, ld .x12 .x19 (ofsO + 8),
   .logic .eor .x .x9 .x9 .x11, .logic .eor .x .x10 .x10 .x12, st .x23 0 .x9, st .x23 8 .x10]

/-- On to the next block (`x24` is zero when none are left). -/
def nextBlock : List Instr := [ptr .x23 .x23 16, ptr .x25 .x25 1, .subImm .x .x24 .x24 1]

/-- A pass over the `x24` whole blocks of the data at `x23` (`x24 > 0`),
with `i` from 1 in `x25`: each block through `body` after its offset. -/
def passScalar (body : List Instr) : Prog isa :=
  .loop (.seq nextOffset (.block (body ++ nextBlock))) (.nonzero .x .x24)

/-- Cache the three most frequent offset increments for an eight-block batch. -/
def passCacheInit : Prog isa :=
  .seq (.block [.ldrq .v0 .x19 l0O])
    (.seq (.block (dbl .x19 l0O lO ++ ([.ldrq .v1 .x19 lO] : List Instr)))
      (.block (dbl .x19 lO lO ++ ([.ldrq .v2 .x19 lO] : List Instr))))

/-- Transfer a cached increment through scalar registers so the following
scalar loads can forward from stores of the same width. -/
def cachedIncrement (v : VReg) : List Instr :=
  [.umov .x .x9 v 0, .umov .x .x10 v 1, st .x19 lO .x9, st .x19 (lO + 8) .x10]

/-- The eighth index is divisible by eight: start from cached L2 and skip
its two already computed doublings. -/
def batchLastIncrement : Prog isa :=
  .seq (.block (cachedIncrement .v2))
    (.seq (.block [.lsr .x .x14 .x25 2])
      (.loop (.block (dbl .x19 lO lO ++ ([.lsr .x .x14 .x14 1] : List Instr) ++ low1)) (.zero .x .x12)))

/-- Where a pass accumulates the checksum relative to XORing the offset. -/
inductive CkMode where
  | none | before | after
  deriving DecidableEq

/-- v3 retains the offset and v5 the checksum across the whole pass. -/
def residentBody (mode : CkMode) : List Instr :=
  ([.ldrq .v4 .x23 0] : List Instr) ++
  (if mode = .before then [.vop (.logic .eor .v5 .v5 .v4)] else []) ++
  ([.vop (.logic .eor .v4 .v4 .v3)] : List Instr) ++
  (if mode = .after then [.vop (.logic .eor .v5 .v5 .v4)] else []) ++
  ([.strq .v4 .x23 0] : List Instr)

def residentStep (v : VReg) (mode : CkMode) : Prog isa :=
  .block (([.vop (.logic .eor .v3 .v3 v)] : List Instr) ++ residentBody mode ++ nextBlock)

def residentLast (mode : CkMode) : Prog isa :=
  .seq batchLastIncrement (.seq (.block [.ldrq .v6 .x19 lO]) (residentStep .v6 mode))

def residentBatch (mode : CkMode) : Prog isa :=
  .seq (residentStep .v0 mode)
    (.seq (residentStep .v1 mode)
      (.seq (residentStep .v0 mode)
        (.seq (residentStep .v2 mode)
          (.seq (residentStep .v0 mode)
            (.seq (residentStep .v1 mode)
              (.seq (residentStep .v0 mode) (residentLast mode)))))))

def passFast (mode : CkMode) (body : List Instr) : Prog isa :=
  .seq (.block [.lsr .x .x9 .x24 3])
    (.ite (.zero .x .x9) (passScalar body)
      (.seq passCacheInit
        (.seq (.block [.ldrq .v3 .x19 ofsO, .ldrq .v5 .x19 ckO])
          (.seq (.loop (.seq (residentBatch mode) (.block [.lsr .x .x9 .x24 3])) (.nonzero .x .x9))
            (.seq (.block [.strq .v3 .x19 ofsO, .strq .v5 .x19 ckO])
              (.ite (.zero .x .x24) (.block []) (passScalar body)))))))

/-- The whole blocks: `pre` (the first pass), `f` on all of them, `post` (the
third pass, the offsets recomputed from `Offset_0`); `x26` their number. -/
def whole (f : Impl.Aes.AArch64.Blocks) (pre post : List Instr) (pm qm : CkMode) : Prog isa :=
  .seq (.block [mov .x23 .x21, mov .x24 .x26, imm .x25 1])
    (.seq (passFast pm pre)
      (.seq (callBlocks f [mov .x2 .x21, mov .x3 .x26])
        (.seq (.block (copy16 o0O ofsO ++ [mov .x23 .x21, mov .x24 .x26, imm .x25 1]))
          (passFast qm post))))

/-! ## The rest of the data and the tag -/

/-- `W + t2O ← pad(P_*)`, `P_*` the `x24` bytes at `x23` (`0 < x24 < 16`),
and add it to the checksum. -/
def padCk : Prog isa := .seq (padTo t2O) (.block (xor16 .x19 t2O ckO))

/-- The `x24` bytes at `x23` XORed with `Pad` at `W + tmpO`. -/
def xorPad : Prog isa :=
  .seq (.block [ptr .x11 .x19 tmpO, mov .x12 .x23, mov .x13 .x24]) xorLoop

/-- The rest of the data (`x24` bytes at `x23`, `x24 > 0`): `Offset_* =
Offset ⊕ L_*`, `Pad = ENCIPHER(K, Offset_*)`; for `seal` (`enc`) the checksum
of the plaintext, then the XOR; for `open`, the XOR, then the checksum. -/
def rest (enc : Bool) : Prog isa :=
  .seq (.block (xor16 .x20 240 ofsO ++ copy16 ofsO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (if enc then .seq padCk xorPad else .seq xorPad padCk))

/-- The tag, `ENCIPHER(K, Checksum ⊕ Offset ⊕ L_$) ⊕ HASH(K, A)`, to `W + d`. -/
def tag (d : Nat) : Prog isa :=
  .seq (.block (copy16 ckO tmpO ++ xor16 .x19 ofsO tmpO ++ xor16 .x19 ldO tmpO))
    (.seq (callBlocks c.enc (oneBlock tmpO))
      (.block (copy16 tmpO d ++ xor16 .x19 sumO d)))

/-! ## The functions -/

/-- The entry of `seal` and `open`: `(ctx = x0, rounds = x1, nonce = x2,
nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7, tag = [sp],
tag_len = [sp + 8], work = [sp + 16])`: the registers saved in `W`, the data
and its length in `x21` and `x28`, the other arguments but `tag` kept in
`W`, `L_$` and `L_0`, the checksum zeroed. -/
def entry : List Instr :=
  ([.ldrSp .x9 16] : List Instr) ++ save .x9 ++
  [mov .x19 .x9, mov .x20 .x0, mov .x21 .x6, mov .x22 .x1, mov .x28 .x7, st .x19 nO .x2,
   st .x19 nlO .x3, st .x19 aadO .x4, st .x19 alenO .x5, .ldrSp .x10 8, st .x19 tlO .x10] ++
  lsetup ++ zero16 ckO

/-- The data: whole blocks, then the rest. -/
def body (enc : Bool) : Prog isa :=
  .seq (.block [.lsr .x .x26 .x28 4])
    (.seq (.ite (.zero .x .x26) (.block [])
        (if enc then whole c.enc (addCk ++ xorOfs) xorOfs .before .none else whole c.dec xorOfs (xorOfs ++ addCk) .none .after))
      (.seq (.block [imm .x10 15, .logic .and .x .x24 .x28 .x10, .sub .x .x9 .x28 .x24,
          .add .x .x23 .x21 .x9])
        (.ite (.zero .x .x24) (.block []) (rest c enc))))

/-- `seal` (`enc`) or `open` up to the tag, at `W + d`: the entry,
`Offset_0`, `HASH`, the data and the tag. -/
def front (enc : Bool) (d : Nat) : Prog isa :=
  .seq (.block entry) (.seq (nonce c) (.seq (hash c) (.seq (body c enc) (tag c d))))

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`, whose
address is at `[sp]`. -/
def tagOut : Prog isa := .seq (.block [.ldrSp .x11 0, mov .x12 .x19, ld .x13 .x19 tlO]) copyLoop

def «seal» : Prog isa := .seq (front c true tagO) (.seq tagOut (.block restore))

/-- The received tag, the `tag_len` bytes at `tag` (whose address is at
`[sp]`), copied to `W`. -/
def recv : Prog isa := .seq (.block [mov .x11 .x19, .ldrSp .x12 0, ld .x13 .x19 tlO]) copyLoop

/-- `open`'s comparison of the first `tag_len` bytes of the tags (at `W` and
`W + t2O`), without a branch: `W + tagO ← 1` if they are equal, else 0. -/
def cmp : Prog isa :=
  .seq (.block [imm .x13 0, mov .x11 .x19, ptr .x12 .x19 t2O, ld .x24 .x19 tlO])
    (.seq (.loop (.block [.ldrb .x9 .x11 0, .ldrb .x10 .x12 0, .logic .eor .x .x9 .x9 .x10,
        .logic .orr .x .x13 .x13 .x9, ptr .x11 .x11 1, ptr .x12 .x12 1, .subImm .x .x24 .x24 1])
        (.nonzero .x .x24))
      (.block [.subImm .x .x13 .x13 1, .lsr .x .x13 .x13 63, st .x19 tagO .x13]))

def maskSmall : Prog isa :=
  .seq (.block [.lsr .x .x9 .x24 4])
    (.ite (.zero .x .x9)
      (.block [.ldrb .x9 .x23 0, .logic .and .w .x9 .x9 .x10, .strb .x9 .x23 0,
        ptr .x23 .x23 1, .subImm .x .x24 .x24 1])
      (.block [.vop (.dup .d2 .v0 .x10), .ldrq .v1 .x23 0, .vop (.logic .and .v1 .v1 .v0),
        .strq .v1 .x23 0, ptr .x23 .x23 16, .subImm .x .x24 .x24 16]))

/-- Mask one vector and advance the payload pointer and remaining count. -/
def maskVector : List Instr :=
  [.vop (.dup .d2 .v0 .x10), .ldrq .v1 .x23 0, .vop (.logic .and .v1 .v1 .v0),
    .strq .v1 .x23 0, ptr .x23 .x23 16, .subImm .x .x24 .x24 16]

def maskVectors : Nat → Prog isa
  | 0 => .block []
  | k+1 => .seq (.block maskVector) (maskVectors k)

def maskChunk : Prog isa :=
  .seq (.block [.lsr .x .x9 .x24 6])
    (.ite (.zero .x .x9) maskSmall (maskVectors 4))

/-- Mask complete vectors, then the remaining bytes, with `0 − ok`. -/
def mask : Prog isa :=
  .seq (.block [mov .x23 .x21, mov .x24 .x28, ld .x9 .x19 tagO, imm .x10 0,
      .sub .x .x10 .x10 .x9])
    (.ite (.zero .x .x24) (.block [])
      (.loop maskChunk (.nonzero .x .x24)))

def «open» : Prog isa :=
  .seq (front c false t2O) (.seq recv (.seq cmp (.seq mask (.block ([ld .x0 .x19 tagO] ++ restore)))))

/-! ## The key setup -/

/-- `vg_aes_ocb_init(key = x0, key_len = x1, ctx = x2, scratch = x3)`: the
registers saved in `scratch` (as `W`), the key expanded into the key
context (with the working space at `scratch + scrO`), then a zero block at
byte 240 enciphered in place, for `L_*`. -/
def init : Prog isa :=
  .seq (.block (save .x3 ++ [mov .x19 .x3, mov .x20 .x2, .lsr .x .x22 .x1 2, ptr .x22 .x22 6,
      ptr .x3 .x19 scrO]))
    (.seq (.call c.key.name c.key.code)
      (.seq (.block [imm .x9 0, st .x20 240 .x9, st .x20 248 .x9, ptr .x2 .x20 240, imm .x3 1,
          mov .x0 .x20, mov .x1 .x22, ptr .x4 .x19 scrO])
        (.seq (.call c.enc.name c.enc.code) (.block restore))))

end VG.Impl.AesOcb.AArch64
