module

public import VerifiedGarbage.Impl.CmacAes.Stream.PPC64LE
public import VerifiedGarbage.Impl.AesCtr.PPC64LE
public import VerifiedGarbage.Impl.Gather.PPC64LE

/-!
# AES-CCM: PPC64LE implementation

`vg_aes_ccm_seal(schedule = r3, rounds = r4, nonce = r5, nonce_len = r6, aad = r7, aad_len = r8, data = r9, len = r10, tag = [r1 + 96], tag_len = [r1 + 104], work = [r1 + 112])`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), with the working space `work` as a last argument, which
a frame on the stack allocates
(`Impl.StackScratch.PPC64LE.withStackScratchArgs`), composed of calls of the
verified `vg_cmac_aes_update`, whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
from a zero block is CCM's CBC-MAC (§6.1 steps 1–4), and `vg_aes_ctr32`, as
on AArch64 (`VG.Impl.AesCcm.AArch64`). PPC64LE has one implementation of
each, so these are not generic over them.

## The working space

`work` (`W`, 2560 bytes): `[0, 16)` the tag `seal` computes, which it then
copies to `tag`, `[32, 48)` a block `B`: `B₀`, the first block of the
associated data or a last block padded with zeros, `[48, 64)` the counter
block `Ctr₀`, `[64, 80)` the counter block passed to `vg_aes_ctr32`,
`[80, 96)` a keystream block, `[96, 112)` the MAC `open` computes,
`[128, 216)` our caller's `r14`–`r23` and our return address, `[216, 248)`
the address and length of the associated data, the length of the nonce and
the address of `tag`, `[256, 288)` the two tags `open` compares, padded with
zeros, and `[384, 2560)` the working space of the functions called
(`vg_cmac_aes_update` needs 2176 bytes). A call (`bl`) stores nothing in
memory, so no stack is used but the frame.

## Registers

`r14` holds `W`, `r15` the tag length, `r16` the key schedule, `r17` the
number of rounds, `r22` the data and `r23` its length throughout; the
functions called preserve them (they are nonvolatile). The pieces take
their arguments in `r18` (a pointer), `r19` (a length), `r20` and `r21`,
which the callees also preserve.

## The pieces

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3), for `q = 15 − n`; `ctrAt` makes
  any `Ctrᵢ` from it by ORing `[i]₆₄` into its last 8 bytes, read and
  written big-endian (`ldbrx`, `stdbrx`; the bytes of `[i]₆₄` before the
  last `q` are zero, as `i < 2^(8q)`).
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), likewise from `Ctr₀`, its first
  byte replaced by the flags; then the MAC state at `W + y` zeroed and `B₀`
  chained into it.
* `aadHead y`: the first block of the associated data, the encoding of its
  length (A.2.2, `header`) followed by as many of its bytes as fit.
* `absorbPad y`: the `r19` bytes at `r18` padded with zeros to whole blocks,
  chained: the whole blocks in one call (of none, possibly), then the last
  bytes in `B`.
* `mac y`: `b0`, the associated data (`aadHead` and `absorbPad`, if there is
  any) and the payload (`absorbPad` of the data), so that `W + y` holds `Yᵣ`.
* `tag y`: `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it.
* `ctr`: the data XORed with the keystream from `Ctr₁`: its whole blocks by
  `vg_aes_ctr32`, in chunks (`ctrChunk`), each from `Ctrⱼ` for its first
  block `j` and ending where the low 32 bits of the counter would wrap
  around, since CCM's counter (A.3) is `q` bytes, up to 8, and
  `vg_aes_ctr32` increments only the low 32 bits; then the last bytes with
  a keystream block. How many blocks a chunk has depends only on the
  length.
* `cmp`: the first `tag_len` bytes of the received tag (at `r18`: `tag`,
  which `open` loads from `W`) and of the computed one (at `W + 96`), padded
  with zeros, compared without a branch: `r21` is 1 if they are equal and 0
  if not.
* `mask`: every byte of the data ANDed with `0 − r21`.
* `tagOut`: the first `tag_len` bytes of the tag at `W` copied to `tag`,
  which `seal` loads from `W`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload
and copies the tag to `tag`; `open` decrypts it, computes the MAC of the
plaintext and the tag at `W + 96`, compares it with the received tag and
masks the data.

The model has no flags: the branches are on whether a register is zero, and
comparisons are the signs of differences of numbers below `2⁶³`. Only the
pointers, `rounds`, the lengths and `tag_len` can affect timing: the
branches are on those, and so are the numbers of calls, bytes copied and
blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesCcm.PPC64LE

open VG.PPC64LE
open VG.Impl.AesCbc.PPC64LE (mov)
open VG.Impl.Gather.PPC64LE (copyBytes)
open VG.Impl.CmacAes.Stream.PPC64LE (updCall)
open VG.Impl.AesCtr.PPC64LE (ctrCall)

/-! ## The working space -/

def bO : Nat := 32
def c0O : Nat := 48
def c1O : Nat := 64
def ksO : Nat := 80
def uO : Nat := 96
def aadO : Nat := 216
def alenO : Nat := 224
def nlenO : Nat := 232
def tagO : Nat := 240
def vO : Nat := 256
def rO : Nat := 272
def scrO : Nat := 384

/-- Our caller's registers, and where we save them (`r14`, the base of the
restore, last). -/
def saved : List (Reg × Nat) :=
  [(.r15, 136), (.r16, 144), (.r17, 152), (.r18, 160), (.r19, 168), (.r20, 176), (.r21, 184),
    (.r22, 192), (.r23, 200), (.r14, 128)]

/-- Where we save the return address. -/
def lrO : Nat := 208

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [.li .r0 0, .store .d .r0 .r14 d, .store .d .r0 .r14 (d + 8)]

/-- XORs the `r4` (at least 1) bytes at `r3` into those at `r9`, advancing
both. -/
def xorBytes : Prog isa :=
  .loop (.block [.lbz .r0 .r3 0, .lbz .r5 .r9 0, .logic .xor .r0 .r0 .r5, .stb .r0 .r9 0,
    .addi .r3 .r3 1, .addi .r9 .r9 1, .subi .r4 .r4 1]) (.nonzero .d .r4)

/-! ## The CBC-MAC -/

/-- `vg_cmac_aes_update`'s arguments but the data and the number of blocks:
the key schedule, the rounds, the MAC state at `W + y` and the working
space. -/
def updArgs (y : Nat) : List Instr := [mov .r3 .r16, mov .r4 .r17, .addi .r5 .r14 y, .addi .r8 .r14 scrO]

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [.addi .r6 .r14 bO, .li .r7 1])) updCall

/-- The last `r21` (`r19 mod 16`, not 0) of the `r19` bytes at `r18`, padded
with zeros in `B`, chained into the MAC state at `W + y`. -/
def absTail (y : Nat) : Prog isa :=
  .seq (.block (zero16 bO ++ [.lsr .d .r10 .r19 4, .lsl .r10 .r10 4, .add .r3 .r18 .r10,
      .addi .r9 .r14 bO, mov .r4 .r21]))
    (.seq copyBytes (updBlock y))

/-- The `r19` bytes at `r18`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [mov .r6 .r18, .lsr .d .r7 .r19 4]))
  (.seq updCall
  (.seq (.block [.li .r9 15, .logic .and .r21 .r19 .r9])
    (.ite (.zero .d .r21) (.block []) (absTail y))))

/-- `B` zeroed, and the encoding (A.2.2) of the length `r19` (not 0) of the
associated data at its start, its length (2, 6 or 10) in `r20`, written
big-endian (`stdbrx`, indexed by `r10`): whether it is below `2³²` is
whether `r19 >> 32` is 0, and whether it is below `2¹⁶ − 2⁸` the sign of
`(r19 >> 8) − 255`. -/
def header : Prog isa :=
  .seq (.block (zero16 bO ++ [.lsr .d .r9 .r19 32]))
  (.ite (.zero .d .r9)
    (.seq (.block [.lsr .d .r9 .r19 8, .subi .r9 .r9 255, .lsr .d .r9 .r9 63])
      (.ite (.zero .d .r9)
        (.block [.lsl .r9 .r19 16, .lis .r10 0xfffe, .lsl .r10 .r10 32, .logic .or .r9 .r9 .r10,
          .li .r10 bO, .storeRev .d .r9 .r14 .r10, .li .r20 6])
        (.block [.lsl .r9 .r19 48, .li .r10 bO, .storeRev .d .r9 .r14 .r10, .li .r20 2])))
    (.block [.li .r9 255, .stb .r9 .r14 bO, .stb .r9 .r14 (bO + 1), .li .r10 (bO + 2),
      .storeRev .d .r19 .r14 .r10, .li .r20 10]))

/-- `r21 := min (16 − r20, r19)`: `min (r19, 16)` by whether `r19 >> 4` is 0,
then the smaller of two numbers of at most 16 by the sign of their
difference. -/
def minK : Prog isa :=
  .seq (.block [.lsr .d .r10 .r19 4])
  (.seq (.ite (.zero .d .r10) (.block [mov .r10 .r19]) (.block [.li .r10 16]))
  (.seq (.block [.li .r9 16, .sub .r9 .r9 .r20, .sub .r11 .r10 .r9, .lsr .d .r11 .r11 63])
    (.ite (.zero .d .r11) (.block [mov .r21 .r9]) (.block [mov .r21 .r10]))))

/-- The first block of the associated data (`r19` bytes at `r18`, at least
one): the encoding of its length followed by its first `min (16 − h, r19)`
bytes, padded with zeros, chained into `W + y`; `r18` and `r19` then the
rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq minK
  (.seq (.block [.add .r9 .r14 .r20, .addi .r9 .r9 bO, mov .r3 .r18, mov .r4 .r21])
  (.seq copyBytes
  (.seq (.block [.add .r18 .r18 .r21, .sub .r19 .r19 .r21]) (updBlock y)))))

/-- The counter block `Ctrᵢ` (A.3), for `i < 2^(8q)` in `r9`, at `W + 64`:
`Ctr₀` with `[i]₆₄` ORed into its last 8 bytes (whose bytes before the last
`q` are zero), read and written big-endian. -/
def ctrAt : List Instr :=
  [.load .d .r10 .r14 c0O, .store .d .r10 .r14 c1O, .li .r11 (c0O + 8), .loadRev .d .r12 .r14 .r11,
    .logic .or .r12 .r12 .r9, .li .r11 (c1O + 8), .storeRev .d .r12 .r14 .r11]

/-- The flags `4 (t − 2) + q − 1 + 64 [a > 0]` (A.2.1, for the even `t`) in
`r9`, with the length of the associated data in `r19`. -/
def flagsSeg : Prog isa :=
  .seq (.block [.subi .r9 .r15 2, .lsl .r9 .r9 2, .load .d .r10 .r14 nlenO, .li .r11 14,
      .sub .r11 .r11 .r10, .add .r9 .r9 .r11])
    (.ite (.zero .d .r19) (.block []) (.block [.addi .r9 .r9 64]))

/-- `B₀` (A.2.1) in `B`, from `Ctr₀` and the flags in `r9`: its first byte
replaced by the flags, and `[p]₆₄` ORed into its last 8 bytes; then the MAC
state at `W + y` zeroed. -/
def b0Seg (y : Nat) : List Instr :=
  [.load .d .r10 .r14 c0O, .load .d .r11 .r14 (c0O + 8), .store .d .r10 .r14 bO,
    .store .d .r11 .r14 (bO + 8), .stb .r9 .r14 bO, .li .r11 (bO + 8), .loadRev .d .r12 .r14 .r11,
    .logic .or .r12 .r12 .r23, .storeRev .d .r12 .r14 .r11] ++ zero16 y

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
def b0 (y : Nat) : Prog isa := .seq flagsSeg (.seq (.block (b0Seg y)) (updBlock y))

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (.block [.load .d .r18 .r14 aadO, .load .d .r19 .r14 alenO])
  (.seq (b0 y)
  (.seq (.ite (.zero .d .r19) (.block []) (.seq (aadHead y) (absorbPad y)))
  (.seq (.block [mov .r18 .r22, mov .r19 .r23]) (absorbPad y))))

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the key schedule, the rounds, the counter block at `W + 64` and the working
space. -/
def ctrArgs : List Instr := [mov .r3 .r16, mov .r4 .r17, .addi .r5 .r14 c1O, .addi .r8 .r14 scrO]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.li .r9 0] ++ ctrAt ++ ctrArgs ++ [.addi .r6 .r14 y, .li .r7 1])) ctrCall

/-! ## Counter mode -/

/-- With `r19` whole blocks left at `r18` and the next counter `j` in `r20`:
`k = min (r19, 2³² − (j mod 2³²))` of them, in `r21`, by `vg_aes_ctr32` from
`Ctrⱼ`, which increments only the low 32 bits of the counter block, and so
gives `Ctrⱼ, …, Ctrⱼ₊ₖ₋₁` as long as they do not wrap around; then `r18`,
`r19` and `r20` are past them. Whether `r19 < 2³² − (j mod 2³²)` is the sign
of their difference. -/
def ctrChunk : Prog isa :=
  .seq (.block [.lsl .r9 .r20 32, .lsr .d .r9 .r9 32, .li .r10 1, .lsl .r10 .r10 32, .sub .r10 .r10 .r9,
      .sub .r11 .r19 .r10, .lsr .d .r11 .r11 63])
  (.seq (.ite (.zero .d .r11) (.block [mov .r21 .r10]) (.block [mov .r21 .r19]))
  (.seq (.block ([mov .r9 .r20] ++ ctrAt ++ ctrArgs ++ [mov .r6 .r18, mov .r7 .r21]))
  (.seq ctrCall
    (.block [.sub .r19 .r19 .r21, .add .r20 .r20 .r21, .lsl .r9 .r21 4, .add .r18 .r18 .r9]))))

/-- The last `r21` (not 0) bytes of the data, at `r18`, XORed with
`CIPH_K(Ctrⱼ)` for `j` in `r20`, which `vg_aes_ctr32` writes over a zero
block. -/
def ctrTail : Prog isa :=
  .seq (.block ([mov .r9 .r20] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [.addi .r6 .r14 ksO, .li .r7 1]))
  (.seq ctrCall
    (.seq (.block [.addi .r3 .r14 ksO, mov .r9 .r18, mov .r4 .r21]) xorBytes))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5): its whole blocks by `ctrChunk`, then its last `len mod 16` bytes
with a keystream block. -/
def ctr : Prog isa :=
  .seq (.block [mov .r18 .r22, .lsr .d .r19 .r23 4, .li .r20 1])
  (.seq (.ite (.zero .d .r19) (.block []) (.loop ctrChunk (.nonzero .d .r19)))
  (.seq (.block [.li .r9 15, .logic .and .r21 .r23 .r9])
    (.ite (.zero .d .r21) (.block []) ctrTail)))

/-! ## Checking the tag -/

/-- The first `r15` (at least 1) bytes of the received tag (at `r18`) and of
the computed one (at `W + 96`), padded with zeros at `W + 272` and
`W + 256`, compared without a branch: `r21` is 1 if they are equal and 0 if
not (`1 − ((d | −d) >> 63)` for the OR `d` of the XORs of their
doublewords). -/
def cmp : Prog isa :=
  .seq (.block (zero16 vO ++ zero16 rO ++ [mov .r3 .r18, .addi .r9 .r14 rO, mov .r4 .r15]))
  (.seq copyBytes
  (.seq (.block [.addi .r3 .r14 uO, .addi .r9 .r14 vO, mov .r4 .r15])
  (.seq copyBytes
    (.block [.load .d .r5 .r14 vO, .load .d .r6 .r14 rO, .logic .xor .r5 .r5 .r6,
      .load .d .r6 .r14 (vO + 8), .load .d .r7 .r14 (rO + 8), .logic .xor .r6 .r6 .r7,
      .logic .or .r5 .r5 .r6, .li .r6 0, .sub .r6 .r6 .r5, .logic .or .r5 .r5 .r6, .lsr .d .r5 .r5 63,
      .li .r21 1, .sub .r21 .r21 .r5]))))

/-- One byte of the data ANDed with the mask `r9`. -/
def maskBody : List Instr :=
  [.lbz .r0 .r3 0, .logic .and .r0 .r0 .r9, .stb .r0 .r3 0, .addi .r3 .r3 1, .subi .r4 .r4 1]

/-- Every byte of the data ANDed with `0 − r21`: all ones if the tags are
equal (`r21` is 1), zeros if not. -/
def mask : Prog isa :=
  .seq (.block [.li .r9 0, .sub .r9 .r9 .r21, mov .r3 .r22, mov .r4 .r23])
    (.ite (.zero .d .r4) (.block []) (.loop (.block maskBody) (.nonzero .d .r4)))

/-! ## The functions -/

/-- Loads `work`, the tag length and `tag` from the stack, saves our caller's
registers and the return address in `work`, and keeps the arguments in
`r14`–`r17`, `r22`, `r23` and `W`. -/
def entry : List Instr :=
  [.addSp .r12 0, .load .d .r11 .r12 112, .mflr .r0] ++ saved.map (fun (r, d) => .store .d r .r11 d) ++
    [.store .d .r0 .r11 lrO, mov .r14 .r11, .load .d .r15 .r12 104, .load .d .r11 .r12 96, mov .r16 .r3,
      mov .r17 .r4, .store .d .r7 .r14 aadO, .store .d .r8 .r14 alenO, .store .d .r6 .r14 nlenO,
      .store .d .r11 .r14 tagO, mov .r22 .r9, mov .r23 .r10]

/-- Restores the return address and our caller's registers (`r14`, the base,
last). -/
def restore : List Instr :=
  [.load .d .r0 .r14 lrO, .mtlr .r0] ++ saved.map (fun (r, d) => .load .d r .r14 d)

/-- `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3) at `W + 48`, for the `r6`-byte nonce at
`r5`: the block zeroed, `14 − n` in its first byte, and the nonce copied
after it. -/
def ctrsSeg : List Instr :=
  zero16 c0O ++ [.li .r9 14, .sub .r9 .r9 .r6, .stb .r9 .r14 c0O, mov .r3 .r5, .addi .r9 .r14 (c0O + 1),
    mov .r4 .r6]

def ctrs : Prog isa := .seq (.block ctrsSeg) copyBytes

/-- The first `r15` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [.load .d .r9 .r14 tagO, mov .r3 .r14, mov .r4 .r15]) copyBytes

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq ctrs (.seq (mac 0) (.seq (tag 0) (.seq ctr (.seq tagOut (.block restore))))))

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa :=
  .seq (.block entry)
  (.seq ctrs
  (.seq ctr
  (.seq (mac uO)
  (.seq (tag uO)
  (.seq (.block [.load .d .r18 .r14 tagO])
  (.seq cmp
  (.seq mask
    (.block ([mov .r3 .r21] ++ restore)))))))))

end VG.Impl.AesCcm.PPC64LE
