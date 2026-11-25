module

public import VerifiedGarbage.Impl.Ed25519.AArch64.Field

/-!
# Field elements in pairs of words, on AArch64

Elements loaded and stored with `ldp` and `stp` (slots 0–13 of the working space, whose offsets
those reach), and the field operations on elements in registers, with the rows and the reduction
of `Word.lean`: sums and differences of any registers, and products that read one operand where
the other's operation left it (`x12`–`x15`). `x10` is zero throughout.
-/

@[expose] public section

namespace VG.Impl.Ed25519.AArch64.Pairs

open VG.AArch64
open VG.Impl.Ed25519.AArch64

/-! ## Elements in registers -/

/-- The element at `o` into four registers. -/
def loadPairs (o : Nat) (a b c d : Reg) : List Instr := [.ldp a b .x0 o, .ldp c d .x0 (o + 16)]

/-- Four registers to the element at `o`. -/
def storePairs (o : Nat) (a b c d : Reg) : List Instr := [.stp a b .x0 o, .stp c d .x0 (o + 16)]

/-! ## Exchanges -/

/-- `t := b, b := a` if the condition is `ne`, else `t := a` (and `b` kept): the swapped `a` is in `t`. -/
def swapWord (t a b : Reg) : List Instr := [.cselc .x t b a .ne, .cselc .x b a b .ne]

/-! ## Sums and differences -/

/-- `a + b` into `d`, its carry folded into the low three words, for a sum below `2²⁵⁶ + 2¹⁹¹`; from
zero in `x10`, with `t` and `u` temporary. -/
def sum3 (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 t u : Reg) : List Instr :=
  [.adds .x d0 a0 b0, .adcs .x d1 a1 b1, .movz .w t 38 0, .adcs .x d2 a2 b2, .adcs .x d3 a3 b3,
    .csel .x u t .x10, .adds .x d0 d0 u, .adcs .x d1 d1 .x10, .adc .x d2 d2 .x10]

/-- `a − b` into `d`, its borrow folded, for `b` below `2²⁵⁶ − 38`. -/
def diff4 (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 t u : Reg) : List Instr :=
  [.subs .x d0 a0 b0, .sbcs .x d1 a1 b1, .movz .w t 38 0, .sbcs .x d2 a2 b2, .sbcs .x d3 a3 b3,
    .csel .x u .x10 t, .subs .x d0 d0 u, .sbcs .x d1 d1 .x10, .sbcs .x d2 d2 .x10, .sbc .x d3 d3 .x10]

/-- `a + b` into `d`, its carry folded into all four words, for a sum below `2²⁵⁷ − 38`. -/
def sum4 (d0 d1 d2 d3 a0 a1 a2 a3 b0 b1 b2 b3 t u : Reg) : List Instr :=
  [.adds .x d0 a0 b0, .adcs .x d1 a1 b1, .movz .w t 38 0, .adcs .x d2 a2 b2, .adcs .x d3 a3 b3,
    .csel .x u t .x10, .adds .x d0 d0 u, .adcs .x d1 d1 .x10, .adcs .x d2 d2 .x10, .adc .x d3 d3 .x10]

/-! ## Products -/

/-- The reduction of the eight words of a product, to the element at `o`. -/
def toSlot (o : Slot) : List Instr := reduceWide ++ storePairs (offset o) .x4 .x5 .x6 .x7

/-- `[o] := [a] · (x12–x15)`. -/
def mulInto (o a : Slot) : List Instr := mulRows (offset a) ++ toSlot o

/-- `[o] := [a] · [b]`. -/
def mulSlots (o a b : Slot) : List Instr :=
  loadPairs (offset b) .x12 .x13 .x14 .x15 ++ mulInto o a

/-- The square of `x12`–`x15`, in eight words. -/
def squareRegs : List Instr := sqrCross ++ sqrDouble ++ sqrDiag

/-- `[o] := [a]²`. -/
def sqrSlots (o a : Slot) : List Instr :=
  loadPairs (offset a) .x12 .x13 .x14 .x15 ++ squareRegs ++ toSlot o

end VG.Impl.Ed25519.AArch64.Pairs
