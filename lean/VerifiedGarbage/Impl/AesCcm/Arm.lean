module

public import VerifiedGarbage.Impl.AesGcm.Arm
public import VerifiedGarbage.Impl.CmacAes.Arm

/-!
# AES-CCM: 32-bit ARM implementation

`vg_aes_ccm_seal(schedule = r0, rounds = r1, nonce = r2, nonce_len = r3, aad = [sp], aad_len = [sp + 4], data = [sp + 8], len = [sp + 12], tag = [sp + 16], tag_len = [sp + 20], work = [sp + 24])`
and `vg_aes_ccm_open` with the same arguments (see `VG.Spec.Ccm.sealContract`
and `openContract`), with the working space `work` as a last argument, which
a frame on the stack allocates (`Impl.StackScratch.Arm.withStackScratch`),
composed of calls of the verified `vg_cmac_aes_update`,
whose chaining (`Cᵢ = CIPH_K(Cᵢ₋₁ ⊕ Mᵢ)`) from a zero block is CCM's CBC-MAC
(§6.1 steps 1–4), and `vg_aes_ctr32`, as on x86-64
(`Impl/AesCcm/X86_64.lean`).

Both callees take two arguments on the stack: a frame pushes them
(`push {r12, lr}`: the number of blocks in `r12` and the working space in
`lr`) around each call, and its pop loads `r12` back. `vg_cmac_aes_update`'s
own frame uses the 8 bytes below that, so the functions use 16 bytes of
stack. The other arguments on the stack are read with `ldr rX, [sp, #off]`
whenever they are needed.

## The working space

`work` (`W`, 2560 bytes): `[0, 16)` the tag `seal` computes, which it then
copies to `tag`, `[32, 48)` a block `B`: `B₀`, the first block of the associated data or a
last block padded with zeros, `[48, 64)` the counter block `Ctr₀`,
`[64, 80)` the counter block passed to `vg_aes_ctr32`, `[80, 96)` a
keystream block, `[112, 128)` the MAC `open` computes, `[128, 164)` our
caller's `r4`–`r11` and our return address `lr`, `[240, 272)` the two tags
`open` compares, padded with zeros, and `[384, 2560)` the working space of
the functions called (`vg_cmac_aes_update` needs 2176 bytes).

## Registers

`r11` holds `W`, `r9` the key schedule, `r8` the number of rounds and `r10`
`q − 1 = 14 − nonce_len` throughout; the functions called preserve them
(they are callee-saved). The pieces take their arguments in `r4` (a
pointer), `r5` (a length) and `r6`, which the callees also preserve.

## The pieces

* `ctrs`: `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3); `ctrAt` makes `Ctrᵢ` from it,
  for `i` in `r0`, by ORing `[i]₃₂` into its last 4 bytes (the bytes of
  `[i]₃₂` before the last `q` are zero, as `i < 2^(8q)`).
* `b0 y`: `B₀ = flags ‖ N ‖ [p]₈q` (A.2.1), likewise from `Ctr₀`, its first
  byte replaced by the flags; then the MAC state at `W + y` zeroed and `B₀`
  chained into it.
* `aad y`: if there is associated data, its first block, the encoding of its
  length (A.2.2, `header`: `aad_len < 2³²` here, so it takes 2 or 6 bytes)
  followed by as many of its bytes as fit (`aadHead`), then the rest
  (`absorbPad`).
* `absorbPad y`: the `r5` bytes at `r4` padded with zeros to whole blocks,
  chained: the whole blocks in one call, then the last bytes in `B`.
* `mac y`: `b0`, `aad` and the payload (`absorbPad` of the data), so that
  `W + y` holds `Yᵣ`.
* `tag y`: `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it.
* `ctr`: the data XORed with the keystream from `Ctr₁`: its whole blocks in
  one call of `vg_aes_ctr32`, which increments only the low 32 bits of the
  counter block, but these never wrap around: `len < 2³²`, so there are
  fewer than `2²⁸` blocks, and when `q < 4` there are fewer than
  `2^(8q)`; then the last bytes with a keystream block.
* `mask`: every byte of the data ANDed with `0 − ok`, for `ok` the result
  of `cmp`.
* `tagOut`: the first `tag_len` bytes of the tag at `W` copied to `tag`.

`seal` computes the MAC of the payload, the tag, then encrypts the payload
and copies the tag to `tag`; `open` decrypts it, computes the MAC of the
plaintext and the tag at `W + 112`, compares the first `tag_len` bytes of it
with the received tag at `tag` without a branch (AES-GCM's `recv` and `cmp`),
and masks the data.

The model branches only on `Z`: `aad_len < 0xff00` takes the carry of a
comparison with `adc`. Only the pointers, `rounds`, the lengths and
`tag_len` can affect timing: the branches are on those, and so are the
numbers of calls, bytes copied and blocks chained.
-/

@[expose] public section

namespace VG.Impl.AesCcm.Arm

open VG.Arm
open VG.Impl.AesGcm.Arm (imm addI save restore ctrFrame copyLoop xorLoop zero16 uO recv cmp)

/-! ## The working space -/

def bO : Nat := 32
def c0O : Nat := 48
def c1O : Nat := 64
def ksO : Nat := 80
def scrO : Nat := 384

/-! ## The calls -/

/-- `vg_cmac_aes_update`, with `n` in `r12` and the working space in `lr`
pushed as its stack arguments. -/
def updFrame : Prog isa :=
  .frame (.push [.r12, .lr]) (.call "vg_cmac_aes_update" Impl.CmacAes.Arm.update) (.pop .r12 8)

/-! ## The CBC-MAC -/

/-- `vg_cmac_aes_update`'s arguments but the data and the number of blocks:
the key schedule, the rounds, the MAC state at `W + y` and the working
space. -/
def updArgs (y : Nat) : List Instr :=
  [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r11 y, addI .lr .r11 scrO]

/-- `B` chained into the MAC state at `W + y`. -/
def updBlock (y : Nat) : Prog isa :=
  .seq (.block (updArgs y ++ [addI .r3 .r11 bO, .mov .r12 (imm 1)])) updFrame

/-- The whole blocks of the `r5` bytes at `r4` chained into `W + y`. -/
def absorbWhole (y : Nat) : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)])
    (.ite .eq (.block []) (.seq (.block (updArgs y ++ [.mov .r3 (.reg .r4)])) updFrame))

/-- The last `r5 mod 16` bytes at `r4`, padded with zeros in `B`, chained
into `W + y`. -/
def absorbTail (y : Nat) : Prog isa :=
  .seq (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.block (zero16 bO ++ [.dp .sub .r1 .r5 (.reg .r6), .dp .add .r1 .r1 (.reg .r4),
          addI .r2 .r11 bO, .mov .r3 (.reg .r6)]))
        (.seq copyLoop (updBlock y))))

/-- The `r5` bytes at `r4`, padded with zeros to whole blocks, chained into
the MAC state at `W + y`. -/
def absorbPad (y : Nat) : Prog isa := .seq (absorbWhole y) (absorbTail y)

/-- `B` zeroed, and the encoding (A.2.2) of the length `r5` (not 0) of the
associated data at its start, its length (2 or 6) in `r6`: `r12` is the
carry of `r5 − 0xff00`, which says whether `0xff00 ≤ r5`. -/
def header : Prog isa :=
  .seq (.block (zero16 bO ++ [.mov .r0 (imm 0xff00), .cmp .r5 (.reg .r0), .mov .r12 (imm 0),
      .adc .r12 .r12 (imm 0), .cmp .r12 (imm 0)]))
  (.ite .eq
    (.block [.rev .r0 .r5, .mov .r0 (.shifted .r0 .lsr 16), .str .r0 .r11 bO, .mov .r6 (imm 2)])
    (.block [.rev .r0 .r5, .mov .r1 (.shifted .r0 .lsl 16), .movw .r2 0xfeff,
      .dp .orr .r1 .r1 (.reg .r2), .str .r1 .r11 bO, .mov .r0 (.shifted .r0 .lsr 16),
      .str .r0 .r11 (bO + 4), .mov .r6 (imm 6)]))

/-- The first block of the associated data (`r5` bytes at `r4`, at least
one): the encoding of its length followed by its first
`r3 = min (16 − h, r5)` bytes (`minLen`), padded with zeros, chained into
`W + y`; `r4` and `r5` then the rest. -/
def aadHead (y : Nat) : Prog isa :=
  .seq header
  (.seq VG.Impl.AesGcm.Arm.minLen
  (.seq (.block [.mov .r1 (.reg .r4), addI .r2 .r11 bO, .dp .add .r2 .r2 (.reg .r6),
      .dp .add .r4 .r4 (.reg .r3), .dp .sub .r5 .r5 (.reg .r3)])
  (.seq copyLoop (updBlock y))))

/-- The associated data, formatted (A.2.2) and chained into `W + y`. -/
def aad (y : Nat) : Prog isa :=
  .seq (.block [.ldrSp .r4 0, .ldrSp .r5 4, .cmp .r5 (imm 0)])
    (.ite .eq (.block []) (.seq (aadHead y) (absorbPad y)))

/-- `Ctr₀ = [q − 1]₈ ‖ N ‖ 0⁸q` (A.3) at `W + 48`, for the `r3`-byte nonce
at `r2`, and `q − 1` in `r10`. -/
def ctrs : Prog isa :=
  .seq (.block (zero16 c0O ++ [.mov .r10 (imm 14), .dp .sub .r10 .r10 (.reg .r3), .strb .r10 .r11 c0O,
      .mov .r1 (.reg .r2), addI .r2 .r11 (c0O + 1)]))
    copyLoop

/-- The counter block `Ctrᵢ` (A.3), for `i < 2^(8q)` in `r0`, at `W + 64`:
`Ctr₀` with `[i]₃₂` ORed into its last 4 bytes (whose bytes before the last
`q` are zero). -/
def ctrAt : List Instr :=
  [.ldr .r1 .r11 c0O, .str .r1 .r11 c1O, .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (c1O + 4),
   .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (c1O + 8), .ldr .r1 .r11 (c0O + 12), .rev .r0 .r0,
   .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 (c1O + 12)]

/-- The flags of `B₀` (A.2.1) in `r0`: `64 [a > 0] + 8 ((t − 2) / 2) + q − 1`,
and `8 ((t − 2) / 2) = 4 t − 8` for the even `t`. -/
def flagsCode : Prog isa :=
  .seq (.block [.ldrSp .r0 20, .mov .r0 (.shifted .r0 .lsl 2), .dp .sub .r0 .r0 (imm 8),
      .dp .add .r0 .r0 (.reg .r10), .ldrSp .r1 4, .cmp .r1 (imm 0)])
    (.ite .eq (.block []) (.block [addI .r0 .r0 64]))

/-- `B₀` in `B`, from `Ctr₀`: its first byte (`q − 1`) replaced by the flags,
and `[p]₃₂` ORed into its last 4 bytes; then the MAC state at `W + y`
zeroed. -/
def b0Block (y : Nat) : List Instr :=
  [.ldr .r1 .r11 c0O, .dp .eor .r1 .r1 (.reg .r10), .dp .orr .r1 .r1 (.reg .r0), .str .r1 .r11 bO,
   .ldr .r1 .r11 (c0O + 4), .str .r1 .r11 (bO + 4), .ldr .r1 .r11 (c0O + 8), .str .r1 .r11 (bO + 8),
   .ldr .r1 .r11 (c0O + 12), .ldrSp .r2 12, .rev .r2 .r2, .dp .orr .r1 .r1 (.reg .r2),
   .str .r1 .r11 (bO + 12)] ++ zero16 y

/-- `B₀` chained into the zeroed MAC state at `W + y`. -/
def b0 (y : Nat) : Prog isa := .seq flagsCode (.seq (.block (b0Block y)) (updBlock y))

/-- `Yᵣ`, the CBC-MAC of the formatted nonce, associated data and payload
(§6.1 steps 1–4), at `W + y`. -/
def mac (y : Nat) : Prog isa :=
  .seq (b0 y) (.seq (aad y) (.seq (.block [.ldrSp .r4 8, .ldrSp .r5 12]) (absorbPad y)))

/-- The arguments of `vg_aes_ctr32` but the data and the number of blocks:
the key schedule, the rounds, the counter block at `W + 64` and the working
space. -/
def ctrArgs : List Instr :=
  [.mov .r0 (.reg .r9), .mov .r1 (.reg .r8), addI .r2 .r11 c1O, addI .lr .r11 scrO]

/-- `Yᵣ ⊕ CIPH_K(Ctr₀)` at `W + y`, by `vg_aes_ctr32` on it with a copy of
`Ctr₀` (which it increments). -/
def tag (y : Nat) : Prog isa :=
  .seq (.block ([.mov .r0 (imm 0)] ++ ctrAt ++ ctrArgs ++ [addI .r3 .r11 y, .mov .r12 (imm 1)]))
    ctrFrame

/-! ## Counter mode -/

/-- The whole blocks of the data (`r5` bytes at `r4`), by `vg_aes_ctr32`
from `Ctr₁`. -/
def ctrWhole : Prog isa :=
  .seq (.block [.mov .r12 (.shifted .r5 .lsr 4), .cmp .r12 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.block ([.mov .r0 (imm 1)] ++ ctrAt ++ ctrArgs ++ [.mov .r3 (.reg .r4)])) ctrFrame))

/-- The last `r5 mod 16` bytes of the data, XORed with `CIPH_K(Ctrⱼ)` for
the block `j` after the whole ones. -/
def ctrTail : Prog isa :=
  .seq (.block [.dp .and .r6 .r5 (imm 15), .cmp .r6 (imm 0)])
    (.ite .eq (.block [])
      (.seq (.block (zero16 ksO ++ [.mov .r0 (.shifted .r5 .lsr 4), addI .r0 .r0 1] ++ ctrAt ++ ctrArgs ++
          [addI .r3 .r11 ksO, .mov .r12 (imm 1)]))
      (.seq ctrFrame
        (.seq (.block [addI .r1 .r11 ksO, .dp .sub .r2 .r5 (.reg .r6), .dp .add .r2 .r2 (.reg .r4),
            .mov .r3 (.reg .r6)]) xorLoop))))

/-- The data XORed with the keystream from `Ctr₁` (§6.1 steps 5–8, §6.2
steps 3–5). -/
def ctr : Prog isa := .seq (.block [.ldrSp .r4 8, .ldrSp .r5 12]) (.seq ctrWhole ctrTail)

/-! ## The tag -/

/-- The first `tag_len` bytes of the tag at `W` copied to `tag`. -/
def tagOut : Prog isa := .seq (.block [.mov .r1 (.reg .r11), .ldrSp .r2 16, .ldrSp .r3 20]) copyLoop

/-! ## Masking the data -/

/-- Every byte of the data ANDed with `0 − ok`, `ok` in `r7`. -/
def mask : Prog isa :=
  .seq (.block [.ldrSp .r4 8, .ldrSp .r5 12, .mov .r1 (imm 0), .dp .sub .r1 .r1 (.reg .r7),
      .cmp .r5 (imm 0)])
    (.ite .eq (.block [])
      (.loop (.block [.ldrb .r12 .r4 0, .dp .and .r12 .r12 (.reg .r1), .strb .r12 .r4 0, addI .r4 .r4 1,
        .subs .r5 .r5 (imm 1)]) .ne))

/-! ## The functions -/

/-- Saves the registers in the working space (`[sp + 24]`), and keeps `W`
in `r11`, the key schedule in `r9` and the rounds in `r8`. -/
def entry : List Instr :=
  .ldrSp .r12 24 :: save .r12 ++ [.mov .r11 (.reg .r12), .mov .r9 (.reg .r0), .mov .r8 (.reg .r1)]

/-- `vg_aes_ccm_seal`. -/
def «seal» : Prog isa :=
  .seq (.block entry) (.seq ctrs (.seq (mac 0) (.seq (tag 0) (.seq ctr (.seq tagOut (.block restore))))))

/-- `vg_aes_ccm_open`, with the received tag at `tag`. -/
def «open» : Prog isa :=
  .seq (.block entry)
  (.seq ctrs
  (.seq ctr
  (.seq (mac uO)
  (.seq (tag uO)
  (.seq (.block [.ldrSp .r6 20])
  (.seq recv
  (.seq (cmp uO)
  (.seq (.block [.mov .r7 (.reg .r0)])
  (.seq mask
    (.block (.mov .r0 (.reg .r7) :: restore)))))))))))

end VG.Impl.AesCcm.Arm
