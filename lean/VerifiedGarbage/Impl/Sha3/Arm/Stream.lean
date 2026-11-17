module

public import VerifiedGarbage.Impl.Sha3.Arm

/-!
# The SHA-3 sponge: ARMv7 implementation

The same structure as the AArch64 implementation. The streaming state is
the Keccak state (`[u64; 25]` at `state`), with the bytes of a partial block
XORed into it as they arrive (see `VG.Spec.Sha3.Repr`); the position in the
block is kept by the caller.

* `absorb(state = r0, rate = r1, pos = r2, data = r3, len = [sp],
  scratch = [sp, #4])` XORs the bytes of `data` into the state from byte
  `pos`, a word at a time while four bytes are left both of the data and of
  the block (`words`) and a byte at a time otherwise, permuting the state
  whenever a block is complete, and returns the position after them.
* `pad(state = r0, rate = r1, pos = r2, suffix = r3, scratch = [sp])` XORs
  the suffix into byte `pos` and `0x80` into byte `rate - 1`, and permutes
  the state.
* `squeeze(state = r0, rate = r1, pos = r2, out = r3, outlen = [sp],
  scratch = [sp, #4])` copies the state to `out` from byte `pos`, a word or
  a byte at a time likewise, permuting it whenever a block has been used up
  and more output is needed, and returns the position after them.

The permutation is called (`vg_keccak_f1600`, `Impl.Sha3.Arm.permute`) with
the first 512 bytes of `scratch` as its scratch space. Its code never writes
`r0` or `r1`, so `state` stays in `r0` and `scratch` in `r1`; it preserves
`r4`–`r11`, so `absorb` and `squeeze` keep their variables in `r4`–`r7`
(`rate`, the position in the block, `data` or `out`, and the bytes of it
left), and save their caller's values of those registers, and their return
address (`lr`, which the calls overwrite), in `scratch[512..532)`.

Byte `pos` of the state is addressed as `[r3]` with `r3 = state + pos`,
and the words of the state and of the data or output at any address, as
the model's `ldr` and `str` allow. Every comparison is a `cmp` or `subs`
tested with `eq`/`ne`. Every address and branch depends only on `sp`, the
pointers, `rate`, `pos` and the lengths.
-/

@[expose] public section

namespace VG.Impl.Sha3.Arm.Stream

open VG.Arm
open VG.Impl.Sha3.Arm (permute)

/-- The callee-saved registers we use (and `lr`), and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) := [(.r4, 512), (.r5, 516), (.r6, 520), (.r7, 524), (.lr, 528)]

/-- Save them, with `scratch` in `r12`. -/
def save : List Instr := saved.map fun (r, d) => .str r .r12 d

/-- Restore them from `scratch` in `r1`. -/
def restore : List Instr := saved.map fun (r, d) => .ldr r .r1 d

/-- Permute the state at `r0`, with scratch space `r1`. -/
def permuteCall : Prog isa := .call "vg_keccak_f1600" permute

/-- Registers: `r0` = `state`, `r1` = `scratch`, `r4` = `rate`, `r5` = the
position in the block, `r6` = `data` or `out`, `r7` = bytes of it left;
then test `r7`. -/
def setup : List Instr :=
  ([.ldrSp .r12 4] : List Instr) ++ save ++
    ([.mov .r4 (.reg .r1), .mov .r1 (.reg .r12), .mov .r5 (.reg .r2), .mov .r6 (.reg .r3),
      .ldrSp .r7 0, .cmp .r7 (.imm 0)] : List Instr)

/-- Return the position, and restore the registers. -/
def epilogue : List Instr := .mov .r0 (.reg .r5) :: restore

/-- `lr :=` the whole words among the bytes that are left both of the data
or the output (`r7`) and of the block (`r4 - r5`): a quarter of the lesser
of the two; and Z is set if there is none. With `r12 = r4 - r5`, the lesser
is `r12 + ((r7 - r12) ∧ m)`, where `m` is all ones if `r7 < r12` (`r7 - r12`
borrows: its carry is clear) and zero otherwise. -/
def words : List Instr :=
  [.dp .sub .r12 .r4 (.reg .r5), .mvn .r3 (.imm 0), .subs .r2 .r7 (.reg .r12), .adc .r3 .r3 (.imm 0),
    .dp .and .r2 .r2 (.reg .r3), .dp .add .r2 .r12 (.reg .r2), .mov .lr (.shifted .r2 .lsr 2),
    .cmp .lr (.imm 0)]

/-- Before `lr` words: take them off the bytes left, `r3 :=` the address of
byte `pos` of the state, and the position after them. -/
def wordsPre : List Instr :=
  [.dp .sub .r7 .r7 (.shifted .lr .lsl 2), .dp .add .r3 .r0 (.reg .r5),
    .dp .add .r5 .r5 (.shifted .lr .lsl 2)]

/-! ## `absorb` -/

/-- A byte of data XORed into the state; Z is set if that completes the block. -/
def absorbByte : List Instr :=
  [.ldrb .r2 .r6 0, .dp .add .r3 .r0 (.reg .r5), .ldrb .r12 .r3 0,
    .dp .eor .r2 .r2 (.reg .r12), .strb .r2 .r3 0, .dp .add .r6 .r6 (.imm 1),
    .dp .add .r5 .r5 (.imm 1), .dp .sub .r7 .r7 (.imm 1), .cmp .r5 (.reg .r4)]

/-- A word of data XORed into the state at `r3`; Z is set after the last of
`lr` words. -/
def absorbWord : List Instr :=
  [.ldr .r2 .r6 0, .ldr .r12 .r3 0, .dp .eor .r2 .r2 (.reg .r12), .str .r2 .r3 0,
    .dp .add .r6 .r6 (.imm 4), .dp .add .r3 .r3 (.imm 4), .subs .lr .lr (.imm 1)]

def absorbBody : Prog isa :=
  .seq (.block words)
  (.seq (.ite .eq (.block absorbByte)
      (.seq (.block wordsPre) (.seq (.loop (.block absorbWord) .ne) (.block [.cmp .r5 (.reg .r4)]))))
    (.seq (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) (.block []))
      (.block [.cmp .r7 (.imm 0)])))

def absorb : Prog isa :=
  .seq (.block setup) (.seq (.ite .eq (.block []) (.loop absorbBody .ne)) (.block epilogue))

/-! ## `pad` -/

def pad : Prog isa :=
  .seq (.block [.ldrSp .r12 0, .str .lr .r12 512,
      .dp .add .r2 .r0 (.reg .r2), .ldrb .lr .r2 0, .dp .eor .lr .lr (.reg .r3), .strb .lr .r2 0,
      .dp .add .r2 .r0 (.reg .r1), .dp .sub .r2 .r2 (.imm 1), .ldrb .lr .r2 0,
      .dp .eor .lr .lr (.imm 0x80), .strb .lr .r2 0, .mov .r1 (.reg .r12)])
  (.seq permuteCall (.block [.ldr .lr .r1 512]))

/-! ## `squeeze` -/

/-- A byte of the state to `out`. -/
def squeezeByte : List Instr :=
  [.dp .add .r3 .r0 (.reg .r5), .ldrb .r2 .r3 0, .strb .r2 .r6 0,
    .dp .add .r6 .r6 (.imm 1), .dp .add .r5 .r5 (.imm 1), .dp .sub .r7 .r7 (.imm 1)]

/-- A word of the state at `r3` to `out`; Z is set after the last of `lr`
words. -/
def squeezeWord : List Instr :=
  [.ldr .r2 .r3 0, .str .r2 .r6 0, .dp .add .r6 .r6 (.imm 4), .dp .add .r3 .r3 (.imm 4),
    .subs .lr .lr (.imm 1)]

def squeezeBody : Prog isa :=
  .seq (.block [.cmp .r5 (.reg .r4)])
  (.seq (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) (.block []))
    (.seq (.block words)
      (.seq (.ite .eq (.block squeezeByte) (.seq (.block wordsPre) (.loop (.block squeezeWord) .ne)))
        (.block [.cmp .r7 (.imm 0)]))))

def squeeze : Prog isa :=
  .seq (.block setup) (.seq (.ite .eq (.block []) (.loop squeezeBody .ne)) (.block epilogue))

end VG.Impl.Sha3.Arm.Stream
