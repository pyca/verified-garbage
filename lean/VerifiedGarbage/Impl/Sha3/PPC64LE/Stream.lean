module

public import VerifiedGarbage.Impl.Sha3.PPC64LE

/-!
# The SHA-3 sponge: PPC64LE implementation

The AArch64 implementation (`Impl/Sha3/AArch64/Stream.lean`), with its
registers renamed. The streaming state is the Keccak state (`[u64; 25]` at
`state`), with the bytes of a partial block XORed into it as they arrive
(see `VG.Spec.Sha3.Repr`); the position in the block is kept by the caller.

* `absorb(state = r3, rate = r4, pos = r5, data = r6, len = r7,
  scratch = r8)` XORs the bytes of `data` into the state from byte `pos`, a
  lane (8 bytes) at a time where the position is at a lane and at least 8
  bytes are left, and a byte at a time otherwise, permuting the state
  whenever a block is complete, and returns the position after them.
* `pad(state = r3, rate = r4, pos = r5, suffix = r6, scratch = r7)` XORs
  the suffix into byte `pos` and `0x80` into byte `rate - 1`, and permutes
  the state.
* `squeeze(state = r3, rate = r4, pos = r5, out = r6, outlen = r7,
  scratch = r8)` copies the state to `out` from byte `pos`, a lane (8 bytes)
  at a time where the position is at a lane and at least 8 bytes are left
  (every rate is a whole number of lanes), and a byte at a time otherwise,
  permuting it whenever a block has been used up and more output is
  needed, and returns the position after them.

The permutation is called (`vg_keccak_f1600`, `Impl.Sha3.PPC64LE.permute`)
with the first 512 bytes of `scratch` as its scratch space. It never writes
`r21`–`r31`, so `absorb` and `squeeze` keep their variables in `r26`–`r31`
(`r26` = `state`, `r27` = `scratch`, `r28` = `rate`, `r29` = the position in
the block, `r30` = `data` or `out`, `r31` = bytes of it left), and save
their caller's values of those registers in `scratch[512..560)`. Our return
address (the link register), which each call replaces, is moved to `r0` and
saved in a stack frame around the whole function.

Only register-plus-displacement addressing is used, so byte `pos` of the
state is addressed as `0(r10)` with `r10 = state + pos` computed just before
the access. The comparison of the position with the rate is a subtraction
tested against zero. Every address and branch depends only on the pointers,
`rate`, `pos` and the lengths.
-/

@[expose] public section

namespace VG.Impl.Sha3.PPC64LE.Stream

open VG.PPC64LE

/-- `mr d, n` (as `addi d, n, 0`; `n` is not `r0`). -/
def mov (d n : Reg) : Instr := .addi d n 0

/-- The nonvolatile registers we use, and where they are saved in `scratch`. -/
def saved : List (Reg × Nat) :=
  [(.r26, 512), (.r27, 520), (.r28, 528), (.r29, 536), (.r30, 544), (.r31, 552)]

/-- Save them, with `scratch` in `b`. -/
def save (b : Reg) : List Instr := saved.map fun (r, d) => .store .d r b d

/-- Restore them from `scratch` in `r27` (`r27`, the base, last). -/
def restore : List Instr :=
  [.load .d .r26 .r27 512, .load .d .r28 .r27 528, .load .d .r29 .r27 536,
    .load .d .r30 .r27 544, .load .d .r31 .r27 552, .load .d .r27 .r27 520]

/-- Permute the state at `r26`, with scratch space `r27`. -/
def permuteAt : Prog isa :=
  .seq (.block [mov .r3 .r26, mov .r4 .r27]) (.call "vg_keccak_f1600" Impl.Sha3.PPC64LE.permute)

/-- Save registers and set up ours. -/
def setup : List Instr :=
  save .r8 ++ [mov .r26 .r3, mov .r27 .r8, mov .r28 .r4, mov .r29 .r5, mov .r30 .r6, mov .r31 .r7]

/-- Run `main` with the link register saved in a frame. -/
def withLr (main : Prog isa) : Prog isa :=
  .seq (.block [.mflr .r0]) (.seq (.frame (.push .r0) main (.pop .r0)) (.block [.mtlr .r0]))

/-! ## `absorb` -/

/-- `r10 = 0` exactly when the position is at a lane (`r29 mod 8 = 0`) and at
least 8 bytes are left (of data or of output) (`r31 ≥ 8`, as `r31 - 8` is
then non-negative). -/
def wordTest : List Instr :=
  [.li .r10 7, .logic .and .r10 .r29 .r10, .subi .r11 .r31 8, .lsr .d .r11 .r11 63,
    .logic .or .r10 .r10 .r11]

/-- A lane of data XORed into the state; `r9 = 0` if that completes the block. -/
def absorbWord : List Instr :=
  [.load .d .r9 .r30 0, .add .r10 .r26 .r29, .load .d .r11 .r10 0, .logic .xor .r9 .r9 .r11,
    .store .d .r9 .r10 0, .addi .r30 .r30 8, .addi .r29 .r29 8, .subi .r31 .r31 8,
    .sub .r9 .r29 .r28]

/-- A byte of data XORed into the state; `r9 = 0` if that completes the block. -/
def absorbByte : List Instr :=
  [.lbz .r9 .r30 0, .add .r10 .r26 .r29, .lbz .r11 .r10 0, .logic .xor .r9 .r9 .r11,
    .stb .r9 .r10 0, .addi .r30 .r30 1, .addi .r29 .r29 1, .subi .r31 .r31 1,
    .sub .r9 .r29 .r28]

def absorbBody : Prog isa :=
  .seq (.block wordTest)
  (.seq (.ite (.zero .d .r10) (.block absorbWord) (.block absorbByte))
    (.ite (.zero .d .r9) (.seq (.block [.li .r29 0]) permuteAt) (.block [])))

/-- `absorb`, but for saving the link register. -/
def absorbMain : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .d .r31) (.block []) (.loop absorbBody (.nonzero .d .r31)))
    (.block (mov .r3 .r29 :: restore)))

def absorb : Prog isa := withLr absorbMain

/-! ## `pad` -/

/-- `pad`, but for saving the link register. -/
def padMain : Prog isa :=
  .seq (.block [.add .r9 .r3 .r5, .lbz .r10 .r9 0, .logic .xor .r10 .r10 .r6,
      .stb .r10 .r9 0, .add .r9 .r3 .r4, .subi .r9 .r9 1, .lbz .r10 .r9 0,
      .li .r11 0x80, .logic .xor .r10 .r10 .r11, .stb .r10 .r9 0, mov .r4 .r7])
    (.call "vg_keccak_f1600" Impl.Sha3.PPC64LE.permute)

def pad : Prog isa := withLr padMain

/-! ## `squeeze` -/

/-- A lane of the state to `out`. -/
def squeezeWord : List Instr :=
  [.add .r10 .r26 .r29, .load .d .r9 .r10 0, .store .d .r9 .r30 0, .addi .r30 .r30 8,
    .addi .r29 .r29 8, .subi .r31 .r31 8]

/-- A byte of the state to `out`. -/
def squeezeByte : List Instr :=
  [.add .r10 .r26 .r29, .lbz .r9 .r10 0, .stb .r9 .r30 0, .addi .r30 .r30 1,
    .addi .r29 .r29 1, .subi .r31 .r31 1]

def squeezeBody : Prog isa :=
  .seq (.block [.sub .r9 .r29 .r28])
  (.seq (.ite (.zero .d .r9) (.seq (.block [.li .r29 0]) permuteAt) (.block []))
    (.seq (.block wordTest) (.ite (.zero .d .r10) (.block squeezeWord) (.block squeezeByte))))

/-- `squeeze`, but for saving the link register. -/
def squeezeMain : Prog isa :=
  .seq (.block setup)
  (.seq (.ite (.zero .d .r31) (.block []) (.loop squeezeBody (.nonzero .d .r31)))
    (.block (mov .r3 .r29 :: restore)))

def squeeze : Prog isa := withLr squeezeMain

end VG.Impl.Sha3.PPC64LE.Stream
