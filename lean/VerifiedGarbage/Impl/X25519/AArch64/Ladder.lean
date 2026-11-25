module

public import VerifiedGarbage.Impl.X25519.AArch64.Word
public import VerifiedGarbage.Impl.Ed25519.AArch64.Divstep
public import VerifiedGarbage.Impl.Ed25519.AArch64.Pairs

/-!
# The X25519 ladder on AArch64

`vg_x25519(out = x0, scalar = x1, point = x2, scratch = x3)`, an internal
function: the ladder of RFC 7748 §5, its operations in the RFC's order, on four
64-bit words an element, with the rows of products and the reduction of
`Impl/Ed25519/AArch64/Word.lean`.

The working space (`x0` from the setup on) holds the field elements in slots of
32 bytes at `64 + 32 n` (`offset`): `x_1, x_2, z_2, x_3, z_3` in slots 0–4 and
`A, B, C, D, AA, BB, E, DA, CB` in slots 5–13, all within the reach of `ldp` and
`stp`; and from byte `BITS` on the bits of the clamped scalar, one to a byte,
with a zero after the last (bit 255). So iteration `t` (counted down in `x19`)
swaps if the bytes `t` and `t + 1` differ, and after the last there is nothing
left to swap, since bit 0 of a clamped scalar is 0.

What an iteration keeps in registers:

* the swap selects the sixteen words of `x_2, z_2, x_3, z_3` into registers
  (`cselc`), from which the sums and differences `A, B, C, D` are formed and
  stored; no swapped element is stored, but `z_3`, for lack of registers;
* a sum or difference that only one product takes is left where that product
  reads an operand (`x12`–`x15`): `DA + CB` and `DA - CB`, which are squared, and
  `AA + a24 E`, a product's other operand;
* every product is stored.

Products and squares are below `2²⁵⁵ + 2¹³⁵` (`fold255`), so the sums fold their
carry once, and `A` and `C`, at most `2²⁵⁶ + 2¹³⁶`, into three words; `AA +
a24 E` is folded at bit 255 with its own products' high halves. `x10` is zero
throughout; `x1`, the output's address, and `x19` are public.
-/

@[expose] public section

namespace VG.Impl.X25519.AArch64.Ladder

open VG.AArch64
open VG.Impl.Ed25519.AArch64 VG.Impl.Ed25519.AArch64.Pairs

/-! ## The swap -/

/-- Bit `t` (`x19`) and bit `t + 1` of the scalar compared: the condition `ne` if they differ. -/
def swapTest : List Instr :=
  [.subImm .x .x19 .x19 1, .add .x .x17 .x0 .x19, .ldrb .x16 .x17 BITS, .ldrb .x17 .x17 (BITS + 1),
    .logic .eor .x .x16 .x16 .x17, .tst .x .x16 .x16]

/-- `x_2` and `x_3` into `x4`–`x7` and `x12`–`x15`, `z_2` and `z_3` into `x21`–`x24` and
`x2, x3, x8, x9`. -/
def loadAll : List Instr :=
  loadPairs (offset 1) .x4 .x5 .x6 .x7 ++ loadPairs (offset 3) .x12 .x13 .x14 .x15 ++
    (loadPairs (offset 2) .x21 .x22 .x23 .x24 ++ loadPairs (offset 4) .x2 .x3 .x8 .x9)

/-- Those swapped: `x_2` and `x_3` in `x11, x4, x5, x6` and `x12`–`x15`, `z_2` and `z_3` in
`x7, x21, x22, x23` and `x2, x3, x8, x9`. -/
def swapRegs : List Instr :=
  swapWord .x11 .x4 .x12 ++ swapWord .x4 .x5 .x13 ++ swapWord .x5 .x6 .x14 ++ swapWord .x6 .x7 .x15 ++
    swapWord .x7 .x21 .x2 ++ swapWord .x21 .x22 .x3 ++ swapWord .x22 .x23 .x8 ++ swapWord .x23 .x24 .x9

/-! ## Sums and differences -/

/-- `A := x_2 + z_2` and `B := x_2 − z_2`, with `z_3` set aside in its slot. -/
def sumsAB : List Instr :=
  storePairs (offset 4) .x2 .x3 .x8 .x9 ++
    sum3 .x16 .x17 .x20 .x24 .x11 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x2 .x3 ++
    storePairs (offset 5) .x16 .x17 .x20 .x24 ++
    diff4 .x11 .x4 .x5 .x6 .x11 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x2 .x3 ++
    storePairs (offset 6) .x11 .x4 .x5 .x6

/-- `C := x_3 + z_3` and `D := x_3 − z_3`. -/
def sumsCD : List Instr :=
  loadPairs (offset 4) .x21 .x22 .x23 .x24 ++
    sum3 .x4 .x5 .x6 .x7 .x12 .x13 .x14 .x15 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 7) .x4 .x5 .x6 .x7 ++
    diff4 .x12 .x13 .x14 .x15 .x12 .x13 .x14 .x15 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 8) .x12 .x13 .x14 .x15

/-! ## Products -/

/-- `E := AA − BB`, also in `x12`–`x15`. -/
def diffE : List Instr :=
  loadPairs (offset 9) .x4 .x5 .x6 .x7 ++ loadPairs (offset 10) .x21 .x22 .x23 .x24 ++
    diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3 ++
    storePairs (offset 11) .x12 .x13 .x14 .x15

/-- `a24 = 121665`. -/
def a24Const : List Instr := [.movz .x .x11 0xdb41 0, .movk .x .x11 1 1]

/-- `AA + a24 E` (`AA` in `x4`–`x7`, `E` in `x12`–`x15`) without the high halves of the three low
products: into `x4`–`x7` and the top word `x20`. -/
def a24Low : List Instr :=
  [.mul .x .x2 .x12 .x11, .mul .x .x3 .x13 .x11, .mul .x .x8 .x14 .x11, .mul .x .x9 .x15 .x11,
    .umulh .x20 .x15 .x11,
    .adds .x .x4 .x4 .x2, .adcs .x .x5 .x5 .x3, .adcs .x .x6 .x6 .x8, .adcs .x .x7 .x7 .x9,
    .adc .x .x20 .x20 .x10]

/-- Those high halves into `x2, x3, x8`, and 19 times the bits from 255 up into `x9`, which leave
`x7`. -/
def a24High : List Instr :=
  [.umulh .x2 .x12 .x11, .umulh .x3 .x13 .x11, .umulh .x8 .x14 .x11,
    .adds .x .x16 .x7 .x7, .adc .x .x9 .x20 .x20, .lsr .x .x7 .x16 1, .movz .w .x11 19 0,
    .mul .x .x9 .x9 .x11]

/-- Their sum, `AA + a24 E`, into `x12`–`x15`. -/
def a24Sum : List Instr :=
  [.adds .x .x12 .x4 .x9, .adcs .x .x13 .x5 .x2, .adcs .x .x14 .x6 .x3, .adc .x .x15 .x7 .x8]

/-- `DA + CB` into `x12`–`x15`. -/
def sumDACB : List Instr :=
  loadPairs (offset 12) .x4 .x5 .x6 .x7 ++ loadPairs (offset 13) .x21 .x22 .x23 .x24 ++
    sum3 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3

/-- `DA − CB` into `x12`–`x15`. -/
def diffDACB : List Instr :=
  loadPairs (offset 12) .x4 .x5 .x6 .x7 ++ loadPairs (offset 13) .x21 .x22 .x23 .x24 ++
    diff4 .x12 .x13 .x14 .x15 .x4 .x5 .x6 .x7 .x21 .x22 .x23 .x24 .x2 .x3

/-! ## The ladder -/

/-- The swaps, and the sums and differences of the swapped elements. -/
def front : List Instr := loadAll ++ (swapTest ++ (swapRegs ++ (sumsAB ++ sumsCD)))

/-- The products of an iteration, those that need each other apart: an operation's carry chains
wait in the core's window for what they need, and the operations after it wait behind them. -/
def back : List (List Instr) := [
  sqrSlots 9 5, sqrSlots 10 6,
  mulSlots 12 8 5, mulSlots 13 7 6,
  diffE, mulSlots 1 9 10,
  loadPairs (offset 9) .x4 .x5 .x6 .x7 ++ loadPairs (offset 11) .x12 .x13 .x14 .x15 ++
    a24Const ++ a24Low ++ a24High ++ a24Sum ++ mulInto 2 11,
  diffDACB ++ squareRegs ++ toSlot 4,
  sumDACB ++ squareRegs ++ toSlot 3,
  mulSlots 4 0 4]

/-- One iteration. -/
def step : List Instr := front ++ back.flatten

/-- The bits `254, …, 0`. -/
def ladder : Prog isa := .loop (.block step) (.nonzero .x .x19)

/-- The working space set up for the ladder (and `x0` its address, `x1` the output's). -/
def setup : List Instr :=
  VG.Impl.X25519.AArch64.save ++ VG.Impl.X25519.AArch64.bits ++
  ([.movz .x .x19 0 0, .strb .x19 .x3 (BITS + 255), mov .x1 .x0, mov .x0 .x3] : List Instr) ++
  loadY ++ store4 (offset 0) ++
  fieldCode [.copy 3 0, .const 1 1, .const 2 0, .const 4 1] ++
  ([.movz .w .x10 0 0, .movz .w .x19 255 0] : List Instr)

def x25519 : Prog isa :=
  .seq (.block setup) <| .seq ladder <| .seq Divstep.invert (.block Word.finish)

end VG.Impl.X25519.AArch64.Ladder
