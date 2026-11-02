module

public import VerifiedGarbage.Impl.Words.RISCV64.Wide
public import VerifiedGarbage.Impl.Words.RISCV64.Bytes
public import VerifiedGarbage.Impl.Words.RISCV64.Loops
public import VerifiedGarbage.Impl.Words64.RISCV64

/-!
# Poly1305: RISC-V implementation

The AArch64 implementation's arithmetic in radix `2⁶⁴`
(`Impl/Poly1305/AArch64/Radix64.lean`), with the carries computed by `sltu`
(`Impl/Words/RISCV64/Wide.lean`), as RV64IM has no carry flag. The
accumulator `h = h0 + 2⁶⁴ h1 + 2¹²⁸ h2` (`h2 ≤ 4` between blocks) is in
`t0`–`t2`, and the clamped `r = r0 + 2⁶⁴ r1` in `a5` and `a6`, with
`s1 = r1 + r1 / 4 = 5 r1 / 4` in `a7` (`r1` is a multiple of 4).

The state (`a0`, 128 bytes, see `VG.Spec.Poly1305.Buffered`):

* `[0, 24)`: the accumulator, fully reduced (`h < p`) between calls, in three
  64-bit words;
* `[24, 56)`: the key: `r` (`[24, 40)`) and `s` (`[40, 56)`);
* `[56, 72)`: the buffer: the message's last bytes that do not fill a block,
  padded in place in `finalize`.

The state, the data and the tag are argument buffers, whose alignment the
contracts do not state, so they are read and written a byte at a time
(`loadLE64`, `storeLE64`). Only temporaries and argument registers are
written, so nothing is saved, and no function uses the stack.

A block `m` is absorbed as on AArch64: `h += m + pad · 2¹²⁸`, then
`x = h0 r0 + h1 s1` and `y = h0 r1 + h1 r0 + h2 s1` (two words each) and
`h2 r0` (one), which `2¹³⁰ ≡ 5` modulo `p = 2¹³⁰ - 5` folds into three words
again. The products are in `t3`–`t6`, with `a4` and `a1` temporaries.

Before `h` is stored, it is reduced fully (`reduce`): `g = h + 5`, and
`g - 2¹³⁰` is selected, with a mask and without a branch, if `g ≥ 2¹³⁰`.

The only branches are on the block count, the number of bytes buffered
(`count mod 16`) and the lengths, and every address is a pointer plus a
constant, or plus a count, so only the pointers, `count` and the lengths can
affect timing.
-/

@[expose] public section

namespace VG.Impl.Poly1305.RISCV64

open VG.RISCV64
open VG.Impl.Words.RISCV64 (mulWide add2 mulAdd mulAddSmall add3 addW3 copyBytes storeBytes copyLoop)
open VG.Impl.Words64.RISCV64 (loadLE64 storeLE64 movImm64)

/-! ## Registers -/

/-- The accumulator. -/
abbrev H0 : Reg := .t0
abbrev H1 : Reg := .t1
abbrev H2 : Reg := .t2
/-- The clamped `r`, and `s1 = 5 r1 / 4`. -/
abbrev R0 : Reg := .a5
abbrev R1 : Reg := .a6
abbrev S1 : Reg := .a7
/-- The products. -/
abbrev X0 : Reg := .t3
abbrev X1 : Reg := .t4
abbrev Y0 : Reg := .t5
abbrev Y1 : Reg := .t6
/-- Temporaries. -/
abbrev T1 : Reg := .a4
abbrev T2 : Reg := .a1

/-! ## The state on entry -/

/-- The clamping mask of `r0`; that of `r1` is it with its two low bits clear. -/
def M0 : BitVec 64 := 0x0ffffffc0fffffff

/-- The clamped `r`, `s1`, and the accumulator, from the state at `a0`. -/
def setup : List Instr :=
  [.load .d R0 .a0 24, .load .d R1 .a0 32] ++ movImm64 T1 T2 M0 ++
  ([.logic .and R0 R0 T1, .logicImm .and T1 T1 (-4), .logic .and R1 R1 T1,
    .shift .srl .d S1 R1 2, .add S1 S1 R1] : List Instr) ++
  [.load .d H0 .a0 0, .load .d H1 .a0 8, .load .d H2 .a0 16]

/-! ## Absorbing a block -/

/-- `h += m`, for the block `m` at `off(b)`, and `h += 2¹²⁸` if `pad`. -/
def addBlock (b : Reg) (off : Nat) (pad : Bool) (wide : Bool := false) : List Instr :=
  (if wide then [.load .d X0 b off, .load .d X1 b (off + 8)]
    else loadLE64 X0 T1 T2 b off ++ loadLE64 X1 T1 T2 b (off + 8)) ++ add3 H0 H1 H2 X0 X1 ++
    (if pad then [.addi H2 H2 1] else [])

/-- `x = h0 r0 + h1 s1` in `t3, t4`, `y = h0 r1 + h1 r0 + h2 s1` in `t5, t6`
and `h2 r0` in `a1`. -/
def products : List Instr :=
  mulWide X0 X1 H0 R0 ++ mulWide Y0 Y1 H0 R1 ++ mulAdd X0 X1 T1 T2 H1 S1 ++
  mulAdd Y0 Y1 T1 T2 H1 R0 ++ mulAddSmall Y0 Y1 T1 H2 S1 ++ ([.mul T2 H2 R0] : List Instr)

/-- `u0 + 2⁶⁴ t = y + x1 + 2⁶⁴ h2 r0`, in `t5, t6`. -/
def combine : List Instr := add2 Y0 Y1 X1 T2

/-- `h = x0 + 2⁶⁴ u0 + 2¹²⁸ (t mod 4) + 5 ⌊t / 4⌋`, where `5 ⌊t / 4⌋ = (t - t mod 4)
+ ⌊t / 4⌋` (`a4`). -/
def fold : List Instr :=
  [.logicImm .and H2 Y1 3, .logicImm .and T1 Y1 (-4), .shift .srl .d T2 Y1 2, .add T1 T1 T2] ++
    addW3 H0 H1 H2 X0 Y0 H2 T1

/-- Absorbing the block at `off(b)`, with `pad` for a whole block (the `0x01`
byte appended to it is `2¹²⁸`), without for a padded last block (whose
`0x01` byte is inside it). -/
def absorb (b : Reg) (off : Nat) (pad : Bool) (wide : Bool := false) : List Instr :=
  addBlock b off pad wide ++ products ++ combine ++ fold

/-! ## The final reduction -/

/-- `g = h + 5`, in `t3`–`t5`. -/
def plus5 : List Instr := .li T1 5 :: addW3 X0 X1 Y0 H0 H1 H2 T1

/-- The mask `⌊g / 2¹³⁰⌋ - 1` (all ones to keep `h`, zero to select `g`) in `a4`,
and `g2 mod 4`. -/
def mask : List Instr :=
  [.shift .srl .d T1 Y0 2, .addi T1 T1 (-1), .logicImm .and Y0 Y0 3]

/-- `h := g ^ ((h ^ g) & mask)`: `h` if the mask is all ones, `g` if it is zero. -/
def selectLimb (h g : Reg) : List Instr :=
  [.logic .xor T2 h g, .logic .and T2 T2 T1, .logic .xor h g T2]

/-- `h` reduced fully. -/
def reduce : List Instr :=
  plus5 ++ mask ++ selectLimb H0 X0 ++ selectLimb H1 X1 ++ selectLimb H2 Y0

/-- `h` stored. -/
def storeH : List Instr :=
  [.store .d H0 .a0 0, .store .d H1 .a0 8, .store .d H2 .a0 16]

/-! ## `init(state = a0, key = a1)` -/

def init : Prog isa :=
  .block (copyBytes .t0 .a1 .a0 0 24 32 ++ storeBytes .t0 .a0 0 (List.replicate 24 0))

/-! ## `blocks(state = a0, blocks = a1, n = a2)`

The blocks are read from `a3`. -/

def body (wide : Bool) : Prog isa :=
  .block (absorb .a3 0 true wide ++ ([.addi .a3 .a3 16, .addi .a2 .a2 (-1)] : List Instr))

def blocks : Prog isa :=
  .seq (.block (.addi .a3 .a1 0 :: setup))
  (.seq (.ite (.zero .a2) (.block []) (.loop (body false) (.nonzero .a2)))
    (.block (reduce ++ storeH)))

/-! ## `update(state = a0, count = a1, data = a2, len = a3)`

With `t6` = the number of bytes in the buffer (`count mod 16`, computed
before `setup`, which writes `a1`), `a2` = the
data not yet consumed and `a3` = its length: a non-empty buffer is filled
from the data (as far as it goes) and, once full, absorbed; then the whole
blocks of the data are absorbed, and the rest is copied into the buffer. -/

/-- The number of bytes to copy into the buffer, `n = min(16 - t6, a3)`, into
`t3`; then `a3 -= n`, the buffer's byte `t6` into `t4`, `t6 += n`, and the
data into `a4` and `a2 += n`. -/
def count : Prog isa :=
  .seq (.block [.li X0 16, .sub X0 X0 Y1])
  (.seq (.ite (.ltu .a3 X0) (.block [.addi X0 .a3 0]) (.block []))
    (.block [.sub .a3 .a3 X0, .addi X1 .a0 56, .add X1 X1 Y1, .add Y1 Y1 X0, .addi T1 .a2 0,
      .add .a2 .a2 X0]))

/-- Fills the buffer with `min(16 - t6, a3)` bytes of the data, and absorbs it
if that fills it. -/
def fill : Prog isa :=
  .seq count
  (.seq (.ite (.zero X0) (.block []) (copyLoop Y0 T1 X1 X0))
  (.seq (.block [.addi X0 Y1 (-16)])
    (.ite (.zero X0) (.block (absorb .a0 56 true)) (.block []))))

/-- Absorbs the whole blocks of the data, from `a2`, counting them in `t3`. -/
def wholeLoop (wide : Bool) : Prog isa :=
  .loop (.block (absorb .a2 0 true wide ++ ([.addi .a2 .a2 16, .addi .a3 .a3 (-16),
    .shift .srl .d X0 .a3 4] : List Instr))) (.nonzero X0)

def whole : Prog isa :=
  .seq (.block [.shift .srl .d X0 .a3 4])
    (.ite (.zero X0) (.block [])
      (.seq (.block [.logicImm .and T1 .a2 7])
        (.ite (.zero T1) (wholeLoop true) (wholeLoop false))))

/-- Copies the rest of the data into the (empty) buffer. -/
def rest : Prog isa :=
  .ite (.zero .a3) (.block []) (.seq (.block [.addi X1 .a0 56]) (copyLoop Y0 .a2 X1 .a3))

def update : Prog isa :=
  .seq (.block (.logicImm .and Y1 .a1 15 :: setup))
  (.seq (.ite (.zero Y1) (.block []) fill)
  (.seq whole
  (.seq rest
    (.block (reduce ++ storeH)))))

/-! ## `finalize(state = a0, count = a1, out = a2)`

`count mod 16`, the number of bytes in the buffer, is in `t6`. A non-empty
buffer is padded in place with `0x01` and zeros and absorbed without `pad`.
Then `h` is reduced, `s` is added, and the low 128 bits of the sum are the
tag. `vg_poly1305_finalize_scratch` is the same code: it does not use its
working space (`a3`). -/

/-- Zeros the buffer from `t4` on, for `t3 > 0` bytes. -/
def zeroBody : List Instr := [.store .b Y0 X1 0, .addi X1 X1 1, .addi X0 X0 (-1)]

def lastBlock : Prog isa :=
  .seq (.block [.li Y0 0, .addi X1 .a0 56, .add X1 X1 Y1, .li X0 16, .sub X0 X0 Y1])
  (.seq (.loop (.block zeroBody) (.nonzero X0))
    (.block (([.li Y0 1, .addi X1 .a0 56, .add X1 X1 Y1, .store .b Y0 X1 0] : List Instr) ++
      absorb .a0 56 false)))

/-- `h += s`, modulo `2¹²⁸`. -/
def addS : List Instr :=
  [.load .d X0 .a0 40, .load .d X1 .a0 48] ++ add2 H0 H1 X0 X1

/-- The tag stored. -/
def storeTag : List Instr := storeLE64 H0 T1 T2 .a2 0 ++ storeLE64 H1 T1 T2 .a2 8

def finalize : Prog isa :=
  .seq (.block (.logicImm .and Y1 .a1 15 :: setup))
  (.seq (.ite (.zero Y1) (.block []) lastBlock)
    (.block (reduce ++ addS ++ storeTag)))

end VG.Impl.Poly1305.RISCV64
