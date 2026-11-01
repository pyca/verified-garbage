module

public import VerifiedGarbage.Impl.CmacAes.Stream.RISCV64
public import VerifiedGarbage.Impl.AesCtr.RISCV64
public import VerifiedGarbage.Impl.Words.RISCV64.Word64

/-!
# AES-CCM: RISC-V implementation

`vg_aes_ccm_seal(schedule = a0, rounds = a1, nonce = a2, nonce_len = a3, aad = a4, aad_len = a5, data = a6, len = a7, tag = [sp], tag_len = [sp + 8], work = [sp + 16])`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), with the working space `work` as a last argument, which
a frame on the stack allocates
(`Impl.StackScratch.RISCV64.withStackScratchArgs`), composed of calls of the
verified `vg_cmac_aes_update`, whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`)
from a zero block is CCM's CBC-MAC (§6.1 steps 1–4), and `vg_aes_ctr32`, as
on PPC64LE (`VG.Impl.AesCcm.PPC64LE`). RISC-V has one implementation of
each, so these are not generic over them.

## The working space

`work` (`W`, 2560 bytes, 8-byte aligned): `[0, 16)` the tag `seal`
computes, which it then copies to `tag`, `[32, 48)` a block `B`: `B₀`, the
first block of the associated data or a last block padded with zeros,
`[48, 64)` the counter block `Ctr₀`, `[64, 80)` the counter block passed to
`vg_aes_ctr32`, `[80, 96)` a keystream block, `[96, 112)` the MAC `open`
computes, `[128, 216)` our caller's `s1`–`s10` and our return address,
`[216, 248)` the address and length of the associated data, the length of
the nonce and the address of `tag`, `[256, 288)` the two tags `open`
compares, padded with zeros, and `[384, 2560)` the working space of the
functions called (`vg_cmac_aes_update` needs 2176 bytes). A call stores
nothing in memory, so no stack is used but the frame.

## Registers

`s1` holds `W`, `s2` the tag length, `s3` the key schedule, `s4` the number
of rounds, `s9` the data and `s10` its length throughout; the functions
called preserve them (they are callee-saved). The pieces take their
arguments in `s5` (a pointer), `s6` (a length), `s7` and `s8`, which the
callees also preserve.

## The pieces

As on PPC64LE:

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3), for `q = 15 − n`; `ctrAt` makes
  any `Ctrᵢ` from it by ORing `[i]₆₄` into its last 8 bytes, read and
  written big-endian a byte at a time (`loadBE64`, `storeBE`; the bytes of
  `[i]₆₄` before the last `q` are zero, as `i < 2^(8q)`).
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), likewise from `Ctr₀`, its first
  byte replaced by the flags; then the MAC state at `W + y` zeroed and `B₀`
  chained into it.
* `aadHead y`: the first block of the associated data, the encoding of its
  length (A.2.2, `header`) followed by as many of its bytes as fit.
* `absorbPad y`: the `s6` bytes at `s5` padded with zeros to whole blocks,
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
* `cmp`: the first `tag_len` bytes of the received tag (at `s5`: `tag`,
  which `open` loads from `W`) and of the computed one (at `W + 96`), padded
  with zeros, compared without a branch: `s8` is 1 if they are equal and 0
  if not.
* `mask`: every byte of the data ANDed with `0 − s8`.
* `tagOut`: the first `tag_len` bytes of the tag at `W` copied to `tag`,
  which `seal` loads from `W`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload
and copies the tag to `tag`; `open` decrypts it, computes the MAC of the
plaintext and the tag at `W + 96`, compares it with the received tag and
masks the data.

The contracts state no alignment for the nonce, the associated data, the
data and the tag, so they are accessed a byte at a time; `W` is aligned. The
branches are on whether a register is zero, and comparisons are `sltu`'s.
Only the pointers, `rounds`, the lengths and `tag_len` can affect timing:
the branches are on those, and so are the numbers of calls, bytes copied
and blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesCcm.RISCV64

open VG.RISCV64 VG.Impl.Words.RISCV64
open VG.Impl.AesCbc.RISCV64 (mov)
open VG.Impl.CmacAes.Stream.RISCV64 (updCall)
open VG.Impl.AesCtr.RISCV64 (ctrCall)

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

/-- Our caller's registers, and where we save them (`s1`, the base of the
restore, last). -/
def saved : List (Reg × Nat) :=
  [(.s2, 136), (.s3, 144), (.s4, 152), (.s5, 160), (.s6, 168), (.s7, 176), (.s8, 184),
    (.s9, 192), (.s10, 200), (.s1, 128)]

/-- Where we save the return address. -/
def raO : Nat := 208

/-- The 16 bytes at `W + d` zeroed. -/
def zero16 (d : Nat) : List Instr := [.li .t0 0, .store .d .t0 .s1 d, .store .d .t0 .s1 (d + 8)]

/-- Copies the `a2` (at least 1) bytes at `a0` to `a1`, advancing both. -/
def copy : Prog isa := copyLoop .t0 .a0 .a1 .a2

/-- XORs the `a2` (at least 1) bytes at `a0` into those at `a1`, advancing
both. -/
def xorBytes : Prog isa :=
  .loop (.block [.load .b .t0 .a0 0, .load .b .t1 .a1 0, .logic .xor .t0 .t0 .t1, .store .b .t0 .a1 0,
    .addi .a0 .a0 1, .addi .a1 .a1 1, .addi .a2 .a2 (-1)]) (.nonzero .a2)

/-! ## The CBC-MAC -/

/-- `vg_cmac_aes_update`'s arguments but the data and the number of blocks:
the key schedule, the rounds, the MAC state at `W + y` and the working
space. -/
def updArgs (y : Nat) : List Instr :=
  [mov .a0 .s3, mov .a1 .s4, .addi .a2 .s1 (y : Int), .addi .a5 .s1 (scrO : Int)]

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [.addi .a3 .s1 (bO : Int), .li .a4 1])) updCall

/-- The last `s8` (`s6 mod 16`, not 0) of the `s6` bytes at `s5`, padded
with zeros in `B`, chained into the MAC state at `W + y`. -/
def absTail (y : Nat) : Prog isa :=
  .seq (.block (zero16 bO ++ [.shift .srl .d .t0 .s6 4, .shift .sll .d .t0 .t0 4, .add .a0 .s5 .t0,
      .addi .a1 .s1 (bO : Int), mov .a2 .s8]))
    (.seq copy (updBlock y))

/-- The `s6` bytes at `s5`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [mov .a3 .s5, .shift .srl .d .a4 .s6 4]))
  (.seq updCall
  (.seq (.block [.logicImm .and .s8 .s6 15])
    (.ite (.zero .s8) (.block []) (absTail y))))

/-- `B` zeroed, and the encoding (A.2.2) of the length `s6` (not 0) of the
associated data at its start, its length (2, 6 or 10) in `s7`, written
big-endian a byte at a time: whether it is below `2³²` is whether
`s6 >> 32` is 0, and whether it is below `2¹⁶ − 2⁸` whether
`s6 >> 8 < 255`. -/
def header : Prog isa :=
  .seq (.block (zero16 bO ++ [.shift .srl .d .t1 .s6 32]))
  (.ite (.zero .t1)
    (.seq (.block [.shift .srl .d .t1 .s6 8, .li .t2 255, .sltu .t1 .t1 .t2])
      (.ite (.zero .t1)
        (.block ([.shift .sll .d .t1 .s6 16, .li .t2 (-2), .shift .sll .d .t2 .t2 48,
          .logic .or .t1 .t1 .t2] ++ storeBE 8 .t1 .t2 .s1 bO ++ [.li .s7 6]))
        (.block ([.shift .sll .d .t1 .s6 48] ++ storeBE 8 .t1 .t2 .s1 bO ++ [.li .s7 2]))))
    (.block ([.li .t1 255, .store .b .t1 .s1 bO, .store .b .t1 .s1 (bO + 1)] ++
      storeBE 8 .s6 .t2 .s1 (bO + 2) ++ [.li .s7 10])))

/-- `s8 := min (16 − s7, s6)`: `min (s6, 16)` by whether `s6 >> 4` is 0,
then the smaller of two numbers of at most 16 by `sltu`. -/
def minK : Prog isa :=
  .seq (.block [.shift .srl .d .t1 .s6 4])
  (.seq (.ite (.zero .t1) (.block [mov .t1 .s6]) (.block [.li .t1 16]))
  (.seq (.block [.li .t2 16, .sub .t2 .t2 .s7, .sltu .t3 .t1 .t2])
    (.ite (.zero .t3) (.block [mov .s8 .t2]) (.block [mov .s8 .t1]))))

/-- The first block of the associated data (`s6` bytes at `s5`, at least
one): the encoding of its length followed by its first `min (16 − h, s6)`
bytes, padded with zeros, chained into `W + y`; `s5` and `s6` then the
rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq minK
  (.seq (.block [.add .a1 .s1 .s7, .addi .a1 .a1 (bO : Int), mov .a0 .s5, mov .a2 .s8])
  (.seq copy
  (.seq (.block [.add .s5 .s5 .s8, .sub .s6 .s6 .s8]) (updBlock y)))))

/-- The counter block `Ctrᵢ` (A.3), for `i < 2^(8q)` in `t3`, at `W + 64`:
`Ctr₀` with `[i]₆₄` ORed into its last 8 bytes (whose bytes before the last
`q` are zero), read and written big-endian. -/
def ctrAt : List Instr :=
  [.load .d .t1 .s1 c0O, .store .d .t1 .s1 c1O] ++ loadBE64 .t1 .t2 .s1 (c0O + 8) ++
    [.logic .or .t1 .t1 .t3] ++ storeBE 8 .t1 .t2 .s1 (c1O + 8)

/-- The flags `4 (t − 2) + q − 1 + 64 [a > 0]` (A.2.1, for the even `t`) in
`t3`, with the length of the associated data in `s6`. -/
def flagsSeg : Prog isa :=
  .seq (.block [.addi .t3 .s2 (-2), .shift .sll .d .t3 .t3 2, .load .d .t1 .s1 nlenO, .li .t2 14,
      .sub .t2 .t2 .t1, .add .t3 .t3 .t2])
    (.ite (.zero .s6) (.block []) (.block [.addi .t3 .t3 64]))

/-- `B₀` (A.2.1) in `B`, from `Ctr₀` and the flags in `t3`: its first byte
replaced by the flags, and `[p]₆₄` ORed into its last 8 bytes; then the MAC
state at `W + y` zeroed. -/
def b0Seg (y : Nat) : List Instr :=
  [.load .d .t1 .s1 c0O, .load .d .t2 .s1 (c0O + 8), .store .d .t1 .s1 bO, .store .d .t2 .s1 (bO + 8),
    .store .b .t3 .s1 bO] ++ loadBE64 .t1 .t2 .s1 (bO + 8) ++ [.logic .or .t1 .t1 .s10] ++
    storeBE 8 .t1 .t2 .s1 (bO + 8) ++ zero16 y

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
def b0 (y : Nat) : Prog isa := .seq flagsSeg (.seq (.block (b0Seg y)) (updBlock y))

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (.block [.load .d .s5 .s1 aadO, .load .d .s6 .s1 alenO])
  (.seq (b0 y)
  (.seq (.ite (.zero .s6) (.block []) (.seq (aadHead y) (absorbPad y)))
  (.seq (.block [mov .s5 .s9, mov .s6 .s10]) (absorbPad y))))

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the key schedule, the rounds, the counter block at `W + 64` and the working
space. -/
def ctrArgs : List Instr :=
  [mov .a0 .s3, mov .a1 .s4, .addi .a2 .s1 (c1O : Int), .addi .a5 .s1 (scrO : Int)]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.li .t3 0] ++ ctrAt ++ ctrArgs ++ [.addi .a3 .s1 (y : Int), .li .a4 1])) ctrCall

/-! ## Counter mode -/

/-- With `s6` whole blocks left at `s5` and the next counter `j` in `s7`:
`k = min (s6, 2³² − (j mod 2³²))` of them, in `s8`, by `vg_aes_ctr32` from
`Ctrⱼ`, which increments only the low 32 bits of the counter block, and so
gives `Ctrⱼ, …, Ctrⱼ₊ₖ₋₁` as long as they do not wrap around; then `s5`,
`s6` and `s7` are past them. Whether `s6 < 2³² − (j mod 2³²)` is `sltu`'s. -/
def ctrChunk : Prog isa :=
  .seq (.block [.shift .sll .d .t1 .s7 32, .shift .srl .d .t1 .t1 32, .li .t2 1, .shift .sll .d .t2 .t2 32,
      .sub .t2 .t2 .t1, .sltu .t1 .s6 .t2])
  (.seq (.ite (.zero .t1) (.block [mov .s8 .t2]) (.block [mov .s8 .s6]))
  (.seq (.block ([mov .t3 .s7] ++ ctrAt ++ ctrArgs ++ [mov .a3 .s5, mov .a4 .s8]))
  (.seq ctrCall
    (.block [.sub .s6 .s6 .s8, .add .s7 .s7 .s8, .shift .sll .d .t1 .s8 4, .add .s5 .s5 .t1]))))

/-- The last `s8` (not 0) bytes of the data, at `s5`, XORed with
`CIPH_K(Ctrⱼ)` for `j` in `s7`, which `vg_aes_ctr32` writes over a zero
block. -/
def ctrTail : Prog isa :=
  .seq (.block ([mov .t3 .s7] ++ ctrAt ++ zero16 ksO ++ ctrArgs ++ [.addi .a3 .s1 (ksO : Int), .li .a4 1]))
  (.seq ctrCall
    (.seq (.block [.addi .a0 .s1 (ksO : Int), mov .a1 .s5, mov .a2 .s8]) xorBytes))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5): its whole blocks by `ctrChunk`, then its last `len mod 16` bytes
with a keystream block. -/
def ctr : Prog isa :=
  .seq (.block [mov .s5 .s9, .shift .srl .d .s6 .s10 4, .li .s7 1])
  (.seq (.ite (.zero .s6) (.block []) (.loop ctrChunk (.nonzero .s6)))
  (.seq (.block [.logicImm .and .s8 .s10 15])
    (.ite (.zero .s8) (.block []) ctrTail)))

/-! ## Checking the tag -/

/-- The first `s2` (at least 1) bytes of the received tag (at `s5`) and of
the computed one (at `W + 96`), padded with zeros at `W + 272` and
`W + 256`, compared without a branch: `s8` is 1 if they are equal and 0 if
not (`1 − (0 < d)` for the OR `d` of the XORs of their doublewords). -/
def cmp : Prog isa :=
  .seq (.block (zero16 vO ++ zero16 rO ++ [mov .a0 .s5, .addi .a1 .s1 (rO : Int), mov .a2 .s2]))
  (.seq copy
  (.seq (.block [.addi .a0 .s1 (uO : Int), .addi .a1 .s1 (vO : Int), mov .a2 .s2])
  (.seq copy
    (.block [.load .d .t0 .s1 vO, .load .d .t1 .s1 rO, .logic .xor .t0 .t0 .t1,
      .load .d .t1 .s1 (vO + 8), .load .d .t2 .s1 (rO + 8), .logic .xor .t1 .t1 .t2,
      .logic .or .t0 .t0 .t1, .li .t1 0, .sltu .t0 .t1 .t0, .li .s8 1, .sub .s8 .s8 .t0]))))

/-- One byte of the data ANDed with the mask `t1`. -/
def maskBody : List Instr :=
  [.load .b .t0 .a0 0, .logic .and .t0 .t0 .t1, .store .b .t0 .a0 0, .addi .a0 .a0 1, .addi .a2 .a2 (-1)]

/-- Every byte of the data ANDed with `0 − s8`: all ones if the tags are
equal (`s8` is 1), zeros if not. -/
def mask : Prog isa :=
  .seq (.block [.li .t1 0, .sub .t1 .t1 .s8, mov .a0 .s9, mov .a2 .s10])
    (.ite (.zero .a2) (.block []) (.loop (.block maskBody) (.nonzero .a2)))

/-! ## The functions -/

/-- Loads `work`, the tag length and `tag` from the stack, saves our caller's
registers and the return address in `work`, and keeps the arguments in
`s1`–`s4`, `s9`, `s10` and `W`. -/
def entry : List Instr :=
  [.addSp .t0 0, .load .d .t1 .t0 16] ++ saved.map (fun (r, d) => .store .d r .t1 d) ++
    [.store .d .ra .t1 raO, mov .s1 .t1, .load .d .s2 .t0 8, .load .d .t1 .t0 0, mov .s3 .a0,
      mov .s4 .a1, .store .d .a4 .s1 aadO, .store .d .a5 .s1 alenO, .store .d .a3 .s1 nlenO,
      .store .d .t1 .s1 tagO, mov .s9 .a6, mov .s10 .a7]

/-- Restores the return address and our caller's registers (`s1`, the base,
last). -/
def restore : List Instr :=
  [.load .d .ra .s1 raO] ++ saved.map (fun (r, d) => .load .d r .s1 d)

/-- `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3) at `W + 48`, for the `a3`-byte nonce at
`a2`: the block zeroed, `14 − n` in its first byte, and the nonce copied
after it. -/
def ctrsSeg : List Instr :=
  zero16 c0O ++ [.li .t1 14, .sub .t1 .t1 .a3, .store .b .t1 .s1 c0O, mov .a0 .a2,
    .addi .a1 .s1 ((c0O + 1 : Nat) : Int), mov .a2 .a3]

def ctrs : Prog isa := .seq (.block ctrsSeg) copy

/-- The first `s2` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [.load .d .a1 .s1 tagO, mov .a0 .s1, mov .a2 .s2]) copy

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
  (.seq (.block [.load .d .s5 .s1 tagO])
  (.seq cmp
  (.seq mask
    (.block ([mov .a0 .s8] ++ restore)))))))))

end VG.Impl.AesCcm.RISCV64
