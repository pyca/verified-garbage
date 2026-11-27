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

A call that runs two or more permutations keeps the state interleaved, in
`scratch`, across them, rather than have each permutation interleave it and
bring it back: `absorb`, at the start of a block with at least two blocks
of data left, absorbs all the whole blocks that are left (`absorbBulk`), and
`squeeze`, when a block has been used up and more than a block of output is
left, squeezes the whole blocks of it (`squeezeBulk`). They call the three
parts of the permutation (`Impl.Sha3.Arm.enterCall`, `roundsCall`,
`leaveCall`) and XOR a block's lanes into the interleaved state, or copy
them out of it, lane by lane (`ladder`). The rounds preserve no register
but `r0` and `r1`, so there the variables are kept in `scratch[532..544)`,
and our caller's `r8`–`r11` in `scratch[544..560)`.

Byte `pos` of the state is addressed as `[r3]` with `r3 = state + pos`,
and the words of the state and of the data or output at any address, as
the model's `ldr` and `str` allow. Every comparison is a `cmp` or `subs`
tested with `eq`/`ne`. Every address and branch depends only on `sp`, the
pointers, `rate`, `pos` and the lengths.
-/

@[expose] public section

namespace VG.Impl.Sha3.Arm.Stream

open VG.Arm
open VG.Impl.Sha3.Arm (permute enterCall roundsCall leaveCall masks xorSeg copySeg)

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

/-! ## Several blocks between one `enter` and one `leave`

`enter` once, then for each block the rounds (`vg_keccak_f1600_rounds`) and
the block's lanes XORed into the interleaved state (`xorSeg`) or copied out
of it (`copySeg`), and `leave` once. The rounds change every register but
`r0` and `r1`, so the variables are kept in `scratch` across them. -/

/-- Where `scratch` keeps `rate`, `data` or `out`, and the bytes of it left. -/
def vRate : Nat := 532
def vPtr : Nat := 536
def vLeft : Nat := 540

/-- Our caller's `r8`–`r11`, which `enter` and the rounds change, and where
they are saved in `scratch`. -/
def savedHi : List (Reg × Nat) := [(.r8, 544), (.r9, 548), (.r10, 552), (.r11, 556)]

/-- Before `enter`: save `r8`–`r11` and the variables. -/
def bulkSave : List Instr :=
  savedHi.map (fun (r, d) => .str r .r1 d) ++ [.str .r4 .r1 vRate, .str .r6 .r1 vPtr, .str .r7 .r1 vLeft]

/-- Before a block's lanes: the masks of the exchanges, `r9` = `data` or
`out`, `r10` = `rate`, `r11` = the bytes left. -/
def bulkLoad : List Instr := masks ++ [.ldr .r9 .r1 vPtr, .ldr .r10 .r1 vRate, .ldr .r11 .r1 vLeft]

/-- After a block's lanes, which advanced `r9`: take the block off the bytes
left, and store the variables. -/
def bulkStore : List Instr :=
  [.dp .sub .r11 .r11 (.reg .r10), .str .r9 .r1 vPtr, .str .r10 .r1 vRate, .str .r11 .r1 vLeft]

/-- After `leave`: the variables in their registers, at the start of a
block, and our caller's `r8`–`r11`. -/
def bulkRestore : List Instr :=
  ([.ldr .r4 .r1 vRate, .ldr .r6 .r1 vPtr, .ldr .r7 .r1 vLeft, .mov .r5 (.imm 0)] : List Instr) ++
    savedHi.map fun (r, d) => .ldr r .r1 d

/-- The lanes `a ≤ j < b` of a block (`seg a b`, with the block's lane `a`
at `r9`), then `r9` after them; and `rest` unless the rate is `8 b`. -/
def rung (seg : Nat → Nat → List Instr) (a b : Nat) (rest : Prog isa) : Prog isa :=
  .seq (.block (seg a b ++
      [.dp .add .r9 .r9 (.imm (BitVec.ofNat 32 (8 * (b - a)))), .cmp .r10 (.imm (BitVec.ofNat 32 (8 * b)))]))
    (.ite .eq (.block []) rest)

/-- The lanes of a block of `rate` (`r10`) bytes, for the rates of
`Spec.Sha3.rates`: 9, 13, 17, 18 or 21 lanes. -/
def ladder (seg : Nat → Nat → List Instr) : Prog isa :=
  rung seg 0 9 (rung seg 9 13 (rung seg 13 17 (rung seg 17 18
    (.block (seg 18 21 ++ [.dp .add .r9 .r9 (.imm (BitVec.ofNat 32 (8 * (21 - 18))))])))))

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

/-- The bytes that are left of the block, or of the data if they are fewer,
XORed into the state, which is permuted if they complete the block. -/
def absorbStep : Prog isa :=
  .seq (.block words)
  (.seq (.ite .eq (.block absorbByte)
      (.seq (.block wordsPre) (.seq (.loop (.block absorbWord) .ne) (.block [.cmp .r5 (.reg .r4)]))))
    (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) (.block [])))

/-- Z is set if the position is 0 and at least two blocks of data are left:
`r3` is zero if `r7 - 2 r4` does not borrow (its carry is set) and `r5` is
zero. -/
def absorbBulkTest : List Instr :=
  [.mvn .r3 (.imm 0), .subs .r2 .r7 (.shifted .r4 .lsl 1), .adc .r3 .r3 (.imm 0),
    .dp .orr .r3 .r3 (.reg .r5), .cmp .r3 (.imm 0)]

/-- Z is set if a block of data is left. -/
def absorbBlockTest : List Instr :=
  [.ldr .r2 .r1 vLeft, .ldr .r3 .r1 vRate, .mvn .r12 (.imm 0), .subs .r2 .r2 (.reg .r3),
    .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]

/-- The whole blocks of the data, from the start of a block: each XORed into
the interleaved state, which the rounds then permute. -/
def absorbBulk : Prog isa :=
  .seq (.block bulkSave) (.seq enterCall
    (.seq (.loop (.seq (.block bulkLoad) (.seq (ladder xorSeg) (.seq (.block bulkStore)
        (.seq roundsCall (.block absorbBlockTest))))) .eq)
      (.seq leaveCall (.block bulkRestore))))

def absorbBody : Prog isa :=
  .seq (.block absorbBulkTest)
    (.seq (.ite .eq absorbBulk absorbStep) (.block [.cmp .r7 (.imm 0)]))

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

/-- Z is clear if more than a block of output is left: `r3` is zero if
`r4 - r7` does not borrow. -/
def squeezeBulkTest : List Instr :=
  [.mvn .r3 (.imm 0), .subs .r2 .r4 (.reg .r7), .adc .r3 .r3 (.imm 0), .cmp .r3 (.imm 0)]

/-- The same, of `r10` and `r11`. -/
def squeezeBlockTest : List Instr :=
  [.mvn .r12 (.imm 0), .subs .r2 .r10 (.reg .r11), .adc .r12 .r12 (.imm 0), .cmp .r12 (.imm 0)]

/-- When a block has been used up and more than a block of output is left:
the rounds permute the interleaved state, and a block of it is copied out,
while more than a block is left; and the rounds permute it once more, for
the output that is left. -/
def squeezeBulk : Prog isa :=
  .seq (.block bulkSave) (.seq enterCall
    (.seq (.loop (.seq roundsCall (.seq (.block bulkLoad) (.seq (ladder copySeg)
        (.block (bulkStore ++ squeezeBlockTest))))) .ne)
      (.seq roundsCall (.seq leaveCall (.block bulkRestore)))))

def squeezeBody : Prog isa :=
  .seq (.block [.cmp .r5 (.reg .r4)])
  (.seq (.ite .eq (.seq (.block squeezeBulkTest)
      (.ite .eq (.seq (.block [.mov .r5 (.imm 0)]) permuteCall) squeezeBulk)) (.block []))
    (.seq (.block words)
      (.seq (.ite .eq (.block squeezeByte) (.seq (.block wordsPre) (.loop (.block squeezeWord) .ne)))
        (.block [.cmp .r7 (.imm 0)]))))

def squeeze : Prog isa :=
  .seq (.block setup) (.seq (.ite .eq (.block []) (.loop squeezeBody .ne)) (.block epilogue))

end VG.Impl.Sha3.Arm.Stream
