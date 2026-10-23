module

public import VerifiedGarbage.Impl.ChaCha20.PPC64LE.Xor
public import VerifiedGarbage.Impl.Poly1305.PPC64LE
public import VerifiedGarbage.Impl.StackScratch.PPC64LE

/-!
# ChaCha20-Poly1305: PPC64LE implementation

`vg_chacha20_poly1305_seal(key = r3, nonce = r4, aad = r5, aad_len = r6,
data = r7, len = r8, tag = r9, work = r10)` and `vg_chacha20_poly1305_open`
(the same arguments, returning `r3`), composed of calls of the verified
ChaCha20 and Poly1305 functions, as on ARMv7 (`Impl/ChaCha20Poly1305/Arm.lean`).
`work` is the working space, which the artifact's frame allocates on the
stack (`withStackScratchWiped`).

The working space (`workLen` = 648 bytes, called the context below):

* `[0, 320)`: the buffer of `vg_chacha20_block` and `vg_chacha20_xor` (the
  first 32 bytes of the block with counter 0 are the one-time Poly1305 key),
  and then the Poly1305 state (`[0, 128)`);
* `[320, 384)`: the ChaCha20 state;
* `[384, 416)`: the one-time key;
* `[416, 432)`: the padded last block of the additional data or the data;
* `[432, 448)`: the lengths block;
* `[448, 464)`: the tag computed by `open`;
* `[464, 520)`: our caller's `r24`–`r29` and our return address;
* `[520, 648)`: the working space of `vg_poly1305_finalize_scratch` (`scratch`).

`r24` holds the context, `r25` the additional data, `r26` its length, `r27`
the data, `r28` its length and `r29` the tag throughout: they are
nonvolatile, and no callee writes them (the callees save and restore
`r14`–`r23` only), so the constant-time analysis sees them public after every
call, which it would not for a register a callee reloads from memory. `r0`,
`r3`–`r6` and `r11`–`r12` are temporaries. The return address is saved in the context, as
`vg_chacha20_xor` does, so the only stack the functions use is
`vg_poly1305_blocks`'s frame.

`count`, the length of the message authenticated, is
`16 (⌈aad_len / 16⌉ + ⌈len / 16⌉ + 1)` modulo 2⁶⁴.

The model has no indexed addressing: a padded last block is copied a byte at
a time through advancing pointers, counting down to zero, and the tags are
compared without a branch, as `1 - ((x | -x) >> 63)` for the OR `x` of the
XORs of their words.

Constant time: only the pointers and the lengths can affect timing (the
branches are on the lengths, and every address is a pointer plus a constant
or a count).
-/

@[expose] public section

namespace VG.Impl.ChaCha20Poly1305.PPC64LE

open VG.PPC64LE
open VG.Impl.ChaCha20.PPC64LE.Xor (mov)

/-! ## Offsets in the context -/

/-- The ChaCha20 state. -/
def stOff : Nat := 320
/-- The one-time key. -/
def keyOff : Nat := 384
/-- The padded last block. -/
def padOff : Nat := 416
/-- The lengths block. -/
def lenOff : Nat := 432
/-- The tag computed, in `open`. -/
def tagOff : Nat := 448
/-- The saved registers, then the return address. -/
def savOff : Nat := 464
/-- The working space of `vg_poly1305_finalize_scratch`. -/
def scrOff : Nat := 520
/-- The size of the working space, in bytes. -/
def workLen : Nat := 648

/-! ## Saving and restoring the registers -/

/-- The registers saved in the context, in order. -/
def saved (i : Nat) : Reg := [.r24, .r25, .r26, .r27, .r28, .r29].getD i .r24

/-- Save them and the return address, with the context in `r10`. -/
def save : List Instr :=
  (List.range 6).flatMap (fun i => [.store .d (saved i) .r10 (savOff + 8 * i)]) ++
    ([.mflr .r0, .store .d .r0 .r10 (savOff + 48)] : List Instr)

/-- Restore them and the return address, through `r12`. -/
def restore : List Instr :=
  ([mov .r12 .r24, .load .d .r0 .r12 (savOff + 48), .mtlr .r0] : List Instr) ++
    (List.range 6).flatMap fun i => [.load .d (saved i) .r12 (savOff + 8 * i)]

/-- The arguments moved to where they are kept. -/
def moves : List Instr :=
  [mov .r24 .r10, mov .r25 .r5, mov .r26 .r6, mov .r27 .r7, mov .r28 .r8, mov .r29 .r9]

/-! ## The ChaCha20 state -/

/-- The ChaCha20 constants. -/
def consts : List (BitVec 32) := [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]

/-- Word `k` of the ChaCha20 state for counter 0 into `r12`: a constant (0–3),
the key (4–11, at `r3`), the counter (12) or the nonce (13–15, at `r4`). -/
def stSrc (k : Nat) : List Instr :=
  if k < 4 then
    let c := consts.getD k 0
    [.lis .r12 (c.extractLsb' 16 16), .ori .r12 .r12 (c.extractLsb' 0 16)]
  else if k < 12 then [.load .w .r12 .r3 (4 * (k - 4))]
  else if k = 12 then [.li .r12 0]
  else [.load .w .r12 .r4 (4 * (k - 13))]

/-- Word `k` of the ChaCha20 state, at `r24 + stOff + 4k`. -/
def stW (k : Nat) : List Instr := stSrc k ++ ([.store .w .r12 .r24 (stOff + 4 * k)] : List Instr)

/-- The ChaCha20 state for counter 0. -/
def initState : List Instr := (List.range 16).flatMap stW

/-- Copies the `n` doublewords at `r24 + a` to `r24 + b`. -/
def copyWords (a b n : Nat) : List Instr :=
  (List.range n).flatMap fun i => [.load .d .r12 .r24 (a + 8 * i), .store .d .r12 .r24 (b + 8 * i)]

/-! ## The calls -/

/-- The block with counter 0 into `ctx[0, 64)`, and its first 32 bytes (the
one-time key) copied to `ctx[384, 416)`. -/
def keyGen : Prog isa :=
  .seq (.block [.addi .r3 .r24 stOff, mov .r4 .r24])
  (.seq (.call "vg_chacha20_block" Impl.ChaCha20.PPC64LE.block)
    (.block (copyWords 0 keyOff 4)))

/-- The Poly1305 state for the one-time key, at `ctx[0, 128)`. -/
def polyInit : Prog isa :=
  .seq (.block [mov .r3 .r24, .addi .r4 .r24 keyOff])
    (.call "vg_poly1305_init" Impl.Poly1305.PPC64LE.init)

/-- `vg_poly1305_blocks`, in its frame. -/
def blocksCode : Prog isa :=
  Impl.StackScratch.PPC64LE.withStackScratch 160 .r6 Impl.Poly1305.PPC64LE.blocks

/-- Absorbs `r5` blocks at `r4`. -/
def absorb : Prog isa :=
  .seq (.block [mov .r3 .r24]) (.call "vg_poly1305_blocks" blocksCode)

/-- Copies the `r12` (nonzero) bytes at `r4` to `r6`, advancing both. -/
def copyLoop : Prog isa :=
  .loop (.block [.lbz .r11 .r4 0, .stb .r11 .r6 0, .addi .r4 .r4 1, .addi .r6 .r6 1,
    .subi .r12 .r12 1]) (.nonzero .d .r12)

/-- The last `r12` bytes (1 to 15), at `r4`, padded with zeros, absorbed. -/
def padTail : Prog isa :=
  .seq (.block [.li .r11 0, .store .d .r11 .r24 padOff, .store .d .r11 .r24 (padOff + 8),
    .addi .r6 .r24 padOff])
  (.seq copyLoop
  (.seq (.block [.addi .r4 .r24 padOff, .li .r5 1]) absorb))

/-- The `n` bytes at `p`, padded with zeros to a multiple of 16, absorbed. -/
def macPad (p n : Reg) : Prog isa :=
  .seq (.block [mov .r4 p, .lsr .d .r5 n 4])
  (.seq absorb
  (.seq (.block [.li .r12 15, .logic .and .r12 n .r12])
    (.ite (.zero .d .r12) (.block [])
      (.seq (.block [.sub .r4 n .r12, .add .r4 p .r4]) padTail))))

/-- The ChaCha20 counter set to 1, and the data encrypted or decrypted. -/
def crypt : Prog isa :=
  .seq (.block [.li .r12 1, .store .w .r12 .r24 (stOff + 48), .addi .r3 .r24 stOff,
    mov .r4 .r27, mov .r5 .r28, mov .r6 .r24])
    (.call "vg_chacha20_xor" Impl.ChaCha20.PPC64LE.Xor.xor)

/-- The lengths block, absorbed. -/
def lengths : Prog isa :=
  .seq (.block [.store .d .r26 .r24 lenOff, .store .d .r28 .r24 (lenOff + 8),
    .addi .r4 .r24 lenOff, .li .r5 1])
    absorb

/-- `⌈n / 16⌉` into `d`, with `t` a temporary: `n / 16 + ((n mod 16) + 15) / 16`. -/
def ceil16 (d t n : Reg) : List Instr :=
  [.lsr .d d n 4, .li t 15, .logic .and t n t, .addi t t 15, .lsr .d t t 4, .add d d t]

/-- The arguments of `vg_poly1305_finalize_scratch`: the state (`r3`), the
length of the message (`r4`), `out` (`r5`, which `out` sets: `tag` for
`seal`, the tag computed for `open`) and `scratch` (`r6`). -/
def finalizeArgs (out : Instr) : List Instr :=
  ceil16 .r4 .r12 .r26 ++ ceil16 .r5 .r12 .r28 ++
  ([.add .r4 .r4 .r5, .addi .r4 .r4 1, .lsl .r4 .r4 4, mov .r3 .r24, out,
    .addi .r6 .r24 scrOff] : List Instr)

/-- The tag computed. -/
def finalize : Prog isa := .call "vg_poly1305_finalize_scratch" Impl.Poly1305.PPC64LE.finalize

/-! ## Seal -/

/-- Up to the tag: the registers saved, the one-time key, the data
encrypted, and the MAC of the additional data, the ciphertext and the
lengths, up to the arguments of `vg_poly1305_finalize_scratch`. -/
def sealMain : Prog isa :=
  .seq (.block (save ++ moves ++ initState))
  (.seq keyGen
  (.seq crypt
  (.seq polyInit
  (.seq (macPad .r25 .r26)
  (.seq (macPad .r27 .r28)
  (.seq lengths
    (.block (finalizeArgs (mov .r5 .r29)))))))))

def «seal» : Prog isa := .seq sealMain (.seq finalize (.block restore))

/-! ## Open -/

/-- Up to the tag: the registers saved, the one-time key, and the MAC of the
additional data, the ciphertext and the lengths, up to the arguments of
`vg_poly1305_finalize_scratch`. -/
def openMain : Prog isa :=
  .seq (.block (save ++ moves ++ initState))
  (.seq keyGen
  (.seq polyInit
  (.seq (macPad .r25 .r26)
  (.seq (macPad .r27 .r28)
  (.seq lengths
    (.block (finalizeArgs (.addi .r5 .r24 tagOff))))))))

/-- `r3 = 1` if the tag computed (at `r24 + 448`) is the one received (at
`r29`), else 0, without a branch: with `x` the OR of the XORs of their
doublewords, `(x | -x) >> 63` is 0 if `x = 0` and 1 otherwise. -/
def compare : List Instr :=
  [.load .d .r3 .r24 tagOff, .load .d .r4 .r29 0, .logic .xor .r3 .r3 .r4,
   .load .d .r4 .r24 (tagOff + 8), .load .d .r5 .r29 8, .logic .xor .r4 .r4 .r5,
   .logic .or .r3 .r3 .r4, .li .r4 0, .sub .r4 .r4 .r3, .logic .or .r3 .r3 .r4,
   .lsr .d .r3 .r3 63, .li .r4 1, .sub .r3 .r4 .r3]

/-- The data decrypted, the tags compared, and the registers restored. -/
def openEnd : Prog isa := .seq crypt (.block (compare ++ restore))

def «open» : Prog isa := .seq openMain (.seq finalize openEnd)

end VG.Impl.ChaCha20Poly1305.PPC64LE
