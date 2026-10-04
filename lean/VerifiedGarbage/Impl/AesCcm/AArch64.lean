import VerifiedGarbage.Impl.AesGcm.AArch64
import VerifiedGarbage.Impl.CmacAes.AArch64.Callee
import VerifiedGarbage.Impl.Aes.AArch64.Callee

/-!
# AES-CCM: AArch64 implementation

`vg_aes_ccm_seal(schedule = x0, rounds = x1, nonce = x2, nonce_len = x3, aad = x4, aad_len = x5, data = x6, len = x7, work = [sp], tag_len = [sp + 8])`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), composed of calls of the verified `vg_cmac_aes_update`,
whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`) from a zero block is CCM's CBC-MAC
(§6.1 steps 1–4), and `vg_aes_ctr32`. They are generic over the
implementations of those they call (`u`, `c`).

## The working space

`work` (`W`, 2560 bytes): `[0, 16)` the tag (the received one, for `open`),
`[32, 48)` a block `B`: `B₀`, the first block of the associated data or a
last block padded with zeros, `[48, 64)` the counter block `Ctr₀`,
`[64, 80)` the counter block passed to `vg_aes_ctr32`, `[80, 96)` a
keystream block, `[96, 112)` the MAC `open` computes, `[128, 216)` our
caller's `x19`–`x28` and our return address `x30`, `[216, 240)` the address
and length of the associated data and the length of the nonce, `[256, 288)`
the two tags `open` compares, padded with zeros, and `[384, 2560)` the
working space of the functions called. A call (`bl`) stores nothing in
memory, so no stack is used.

## Registers

`x19` holds `W`, `x20` the tag length, `x21` the key schedule, `x22` the
number of rounds, `x27` the data and `x28` its length throughout; the
functions called preserve them. The pieces take their arguments in `x23`
(a pointer), `x24` (a length), `x25` and `x26`, which the callees also
preserve.

## The pieces

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3), for `q = 15 − n`; `ctrAt` makes
  any `Ctrᵢ` from it by ORing `[i]₆₄` into its last 8 bytes (the bytes of
  `[i]₆₄` before the last `q` are zero, as `i < 2^(8q)`).
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), likewise from `Ctr₀`, its first
  byte replaced by the flags; then the MAC state at `W + y` zeroed and `B₀`
  chained into it.
* `aadHead y`: the first block of the associated data, the encoding of its
  length (A.2.2, `header`) followed by as many of its bytes as fit.
* `absorbPad y`: the `x24` bytes at `x23` padded with zeros to whole blocks,
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
* `cmp`: the first `tag_len` bytes of the received tag (at `W`) and of the
  computed one (at `W + 96`), padded with zeros, compared without a branch:
  `x10` is 0 if they are equal and 1 if not.
* `mask`: every byte of the data ANDed with `x10 − 1`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload;
`open` decrypts it, computes the MAC of the plaintext and the tag at
`W + 96`, compares them and masks the data.

The model has no flags or register-offset addressing: the branches are
`cbz`/`cbnz`, and bytes are copied through advancing pointers. Only the
pointers, `rounds`, the lengths and `tag_len` can affect timing: the
branches are on those, and so are the numbers of calls, bytes copied and
blocks chained.
-/

namespace VG.Impl.AesCcm.AArch64

open VG.AArch64
open VG.Impl.AesGcm.AArch64 (mov ptr imm save restore copyLoop xorLoop minK)

/-! ## The working space -/

def bO : Nat := 32
def c0O : Nat := 48
def c1O : Nat := 64
def ksO : Nat := 80
def uO : Nat := 96
def aadO : Nat := 216
def alenO : Nat := 224
def nlenO : Nat := 232
def vO : Nat := 256
def rO : Nat := 272
def scrO : Nat := 384

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [imm .x9 0, .str .x .x9 .x19 d, .str .x .x9 .x19 (d + 8)]

variable (u : Impl.CmacAes.AArch64.Update) (c : Impl.Aes.AArch64.Ctr32)

def callUpdate : Prog isa := .call u.name u.code

def callCtr : Prog isa := .call c.name c.code

/-! ## The CBC-MAC -/

/-- `vg_cmac_aes_update`'s arguments but the data and the number of blocks:
the key schedule, the rounds, the MAC state at `W + y` and the working
space. -/
def updArgs (y : Nat) : List Instr := [mov .x0 .x21, mov .x1 .x22, ptr .x2 .x19 y, ptr .x5 .x19 scrO]

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [ptr .x3 .x19 bO, imm .x4 1])) (callUpdate u)

/-- The last `x24 mod 16` (not 0) bytes of the `x24` bytes at `x23`, padded
with zeros in `B`, chained into the MAC state at `W + y`. -/
def absTail (y : Nat) : Prog isa :=
  .seq (.block (zero16 bO ++ [.lsr .x .x10 .x24 4, .lsl .x .x10 .x10 4, .add .x .x12 .x23 .x10,
      ptr .x11 .x19 bO]))
    (.seq copyLoop (updBlock u y))

/-- The `x24` bytes at `x23`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [mov .x3 .x23, .lsr .x .x4 .x24 4]))
  (.seq (callUpdate u)
  (.seq (.block [imm .x9 15, .logic .and .x .x13 .x24 .x9])
    (.ite (.zero .x .x13) (.block []) (absTail u y))))

/-- `B` zeroed, and the encoding (A.2.2) of the length `x24` (not 0) of the
associated data at its start, its length (2, 6 or 10) in `x25`: whether it is
below `2³²` is whether `x24 >> 32` is 0, and whether it is below `2¹⁶ − 2⁸`
the sign of `(x24 >> 8) − 255`. -/
def header : Prog isa :=
  .seq (.block (zero16 bO ++ [.lsr .x .x9 .x24 32]))
  (.ite (.zero .x .x9)
    (.seq (.block [.lsr .x .x9 .x24 8, .subImm .x .x9 .x9 255, .lsr .x .x9 .x9 63])
      (.ite (.zero .x .x9)
        (.block [.rev .x9 .x24, .lsr .x .x9 .x9 16, .movz .x .x10 0xfeff 0, .logic .orr .x .x9 .x9 .x10,
          .str .x .x9 .x19 bO, imm .x25 6])
        (.block [.rev .x9 .x24, .lsr .x .x9 .x9 48, .str .x .x9 .x19 bO, imm .x25 2])))
    (.block [.movz .x .x9 0xffff 0, .str .x .x9 .x19 bO, .rev .x9 .x24, ptr .x10 .x19 (bO + 2),
      .str .x .x9 .x10 0, imm .x25 10]))

/-- The first block of the associated data (`x24` bytes at `x23`, at least
one): the encoding of its length followed by its first `min (16 − h, x24)`
bytes, padded with zeros, chained into `W + y`; `x23` and `x24` then the
rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq minK
  (.seq (.block [.add .x .x11 .x19 .x25, ptr .x11 .x11 bO, mov .x12 .x23, mov .x13 .x10])
  (.seq copyLoop
  (.seq (.block [.add .x .x23 .x23 .x10, .sub .x .x24 .x24 .x10]) (updBlock u y)))))

/-- The counter block `Ctrᵢ` (A.3), for `i < 2^(8q)` in `x9`, at `W + 64`:
`Ctr₀` with `[i]₆₄` ORed into its last 8 bytes (whose bytes before the last
`q` are zero). -/
def ctrAt : List Instr :=
  [.ldr .x .x10 .x19 c0O, .ldr .x .x11 .x19 (c0O + 8), .str .x .x10 .x19 c1O, .rev .x9 .x9,
    .logic .orr .x .x11 .x11 .x9, .str .x .x11 .x19 (c1O + 8)]

/-- The flags `4 (t − 2) + q − 1 + 64 [a > 0]` (A.2.1, for the even `t`) in
`x9`, with the length of the associated data in `x24`. -/
def flagsSeg : Prog isa :=
  .seq (.block [.subImm .x .x9 .x20 2, .lsl .x .x9 .x9 2, .ldr .x .x10 .x19 nlenO, imm .x11 14,
      .sub .x .x11 .x11 .x10, .add .x .x9 .x9 .x11])
    (.ite (.zero .x .x24) (.block []) (.block [.addImm .x .x9 .x9 64]))

/-- `B₀` (A.2.1) in `B`, from `Ctr₀` and the flags in `x9`: its first byte
replaced by the flags, and `[p]₆₄` ORed into its last 8 bytes; then the MAC
state at `W + y` zeroed. -/
def b0Seg (y : Nat) : List Instr :=
  [.ldr .x .x10 .x19 c0O, .ldr .x .x11 .x19 (c0O + 8), .str .x .x10 .x19 bO, .strb .x9 .x19 bO,
    .rev .x12 .x28, .logic .orr .x .x11 .x11 .x12, .str .x .x11 .x19 (bO + 8)] ++ zero16 y

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
def b0 (y : Nat) : Prog isa := .seq flagsSeg (.seq (.block (b0Seg y)) (updBlock u y))

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (.block [.ldr .x .x23 .x19 aadO, .ldr .x .x24 .x19 alenO])
  (.seq (b0 u y)
  (.seq (.ite (.zero .x .x24) (.block []) (.seq (aadHead u y) (absorbPad u y)))
  (.seq (.block [mov .x23 .x27, mov .x24 .x28]) (absorbPad u y))))

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the key schedule, the rounds, the counter block at `W + 64` and the working
space. -/
def ctrArgs : List Instr := [mov .x0 .x21, mov .x1 .x22, ptr .x2 .x19 c1O, ptr .x5 .x19 scrO]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([imm .x9 0] ++ ctrAt ++ ctrArgs ++ [ptr .x3 .x19 y, imm .x4 1])) (callCtr c)

/-! ## Counter mode -/

/-- With `x24` whole blocks left at `x23` and the next counter `j` in `x25`:
`k = min (x24, 2³² − (j mod 2³²))` of them, in `x26`, by `vg_aes_ctr32` from
`Ctrⱼ`, which increments only the low 32 bits of the counter block, and so
gives `Ctrⱼ, …, Ctrⱼ₊ₖ₋₁` as long as they do not wrap around; then `x23`,
`x24` and `x25` are past them. Whether `x24 < 2³² − (j mod 2³²)` is the sign
of their difference. -/
def ctrChunk : Prog isa :=
  .seq (.block [.addImm .w .x9 .x25 0, .movz .x .x10 1 2, .sub .x .x10 .x10 .x9, .sub .x .x11 .x24 .x10,
      .lsr .x .x11 .x11 63])
  (.seq (.ite (.zero .x .x11) (.block [mov .x26 .x10]) (.block [mov .x26 .x24]))
  (.seq (.block ([mov .x9 .x25] ++ ctrAt ++ ctrArgs ++ [mov .x3 .x23, mov .x4 .x26]))
  (.seq (callCtr c)
    (.block [.sub .x .x24 .x24 .x26, .add .x .x25 .x25 .x26, .lsl .x .x9 .x26 4, .add .x .x23 .x23 .x9]))))

/-- The last `x26` (not 0) bytes of the data, at `x23`, XORed with
`CIPH_K(Ctrⱼ)` for `j` in `x25`, which `vg_aes_ctr32` writes over a zero
block. -/
def ctrTail : Prog isa :=
  .seq (.block ([mov .x9 .x25] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [ptr .x3 .x19 ksO, imm .x4 1]))
  (.seq (callCtr c)
    (.seq (.block [ptr .x11 .x19 ksO, mov .x12 .x23, mov .x13 .x26]) xorLoop))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5): its whole blocks by `ctrChunk`, then its last `len mod 16` bytes
with a keystream block. -/
def ctr : Prog isa :=
  .seq (.block [mov .x23 .x27, .lsr .x .x24 .x28 4, imm .x25 1])
  (.seq (.ite (.zero .x .x24) (.block []) (.loop (ctrChunk c) (.nonzero .x .x24)))
  (.seq (.block [imm .x9 15, .logic .and .x .x26 .x28 .x9])
    (.ite (.zero .x .x26) (.block []) (ctrTail c))))

/-! ## Checking the tag -/

/-- The first `x20` (at least 1) bytes of the received tag (at `W`) and of
the computed one (at `W + 96`), padded with zeros at `W + 272` and
`W + 256`, compared: `x10` is 0 if they are equal and 1 if not (the carry of
adding all ones to their difference). -/
def cmp : Prog isa :=
  .seq (.block [imm .x9 0, .str .x .x9 .x19 vO, .str .x .x9 .x19 (vO + 8), .str .x .x9 .x19 rO,
      .str .x .x9 .x19 (rO + 8), ptr .x11 .x19 rO, mov .x12 .x19, mov .x13 .x20])
  (.seq copyLoop
  (.seq (.block [ptr .x11 .x19 vO, ptr .x12 .x19 uO, mov .x13 .x20])
  (.seq copyLoop
    (.block [.ldr .x .x9 .x19 vO, .ldr .x .x10 .x19 rO, .logic .eor .x .x9 .x9 .x10,
      .ldr .x .x10 .x19 (vO + 8), .ldr .x .x11 .x19 (rO + 8), .logic .eor .x .x10 .x10 .x11,
      .logic .orr .x .x9 .x9 .x10, imm .x11 0, .subImm .x .x12 .x11 1, .adds .x .x9 .x9 .x12,
      .adcs .x .x10 .x11 .x11]))))

/-- One byte of the data ANDed with the mask `x11`. -/
def maskBody : List Instr :=
  [.ldrb .x14 .x12 0, .logic .and .w .x14 .x14 .x11, .strb .x14 .x12 0, .addImm .x .x12 .x12 1,
    .subImm .x .x13 .x13 1]

/-- Every byte of the data ANDed with `x10 − 1`: all ones if the tags are
equal (`x10` is 0), zeros if not. -/
def mask : Prog isa :=
  .seq (.block [.subImm .x .x11 .x10 1, mov .x12 .x27, mov .x13 .x28])
    (.ite (.zero .x .x13) (.block []) (.loop (.block maskBody) (.nonzero .x .x13)))

/-! ## The functions -/

/-- Loads `work` and the tag length from the stack, saves our caller's
registers in `work`, and keeps the arguments in `x19`–`x22`, `x27`, `x28`
and `W`. -/
def entry : List Instr :=
  [.ldrSp .x9 0, .ldrSp .x10 8] ++ save .x9 ++
    [mov .x19 .x9, mov .x20 .x10, mov .x21 .x0, mov .x22 .x1, .str .x .x4 .x19 aadO,
      .str .x .x5 .x19 alenO, .str .x .x3 .x19 nlenO, mov .x27 .x6, mov .x28 .x7]

/-- `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3) at `W + 48`, for the `x3`-byte nonce at
`x2`: the block zeroed, `14 − n` in its first byte, and the nonce copied
after it. -/
def ctrsSeg : List Instr :=
  [imm .x9 0, .str .x .x9 .x19 c0O, .str .x .x9 .x19 (c0O + 8), imm .x9 14, .sub .x .x9 .x9 .x3,
    .strb .x9 .x19 c0O, ptr .x11 .x19 (c0O + 1), mov .x12 .x2, mov .x13 .x3]

def ctrs : Prog isa := .seq (.block ctrsSeg) copyLoop

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq ctrs (.seq (mac u 0) (.seq (tag c 0) (.seq (ctr c) (.block restore)))))

/-- `vg_aes_ccm_open`. -/
def «open» : Prog isa :=
  .seq (.block entry)
  (.seq ctrs
  (.seq (ctr c)
  (.seq (mac u uO)
  (.seq (tag c uO)
  (.seq cmp
  (.seq (.block [imm .x0 1, .sub .x .x0 .x0 .x10])
  (.seq mask
    (.block restore))))))))

end VG.Impl.AesCcm.AArch64
