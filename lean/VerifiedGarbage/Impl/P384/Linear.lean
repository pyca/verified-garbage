module

public import VerifiedGarbage.Impl.P384.Ops

/-!
# P-384's small linear combinations on AArch64

`lin98`, `lin41` and `lin38` write `9A - 8B`, `4A - B` and `3A - 8B` modulo `p`,
for `A` and `B` below `p` in slots, without multiplications. With `B' = p - B`
the sum `cA + dB'` is at least zero, and is built from shifts and additions in
seven words, as `8(A + B') + A`, `4A + B'` and `2(4B' + A) + A`. Its top word
`t` is small, and `2^384 = p + c` with `c = 2^128 + 2^96 - 2^32 + 1`: the words
of `t c`, added to the low six, leave less than `2p` (`fold`).
-/

@[expose] public section

namespace VG.Impl.P384.Linear
open VG.AArch64 VG.Impl.Mont VG.Impl.Mont.AArch64
open VG.Impl.P384.Ops (M)

/-- `A`'s words. -/
abbrev aw : List Reg := [.x1, .x3, .x4, .x5, .x6, .x16]
/-- `B`'s words, and then `p - B`'s. -/
abbrev bw : List Reg := [.x17, .x21, .x22, .x23, .x24, .x25]
/-- The sum's low six words; `x14` is the seventh. -/
abbrev sw : List Reg := [.x8, .x9, .x10, .x11, .x12, .x13]

/-- The words above a word `b` of a number shifted left by `k`, high ones first:
`ds` may be `ss`. The words past the end of `ss` are the bits shifted out. -/
def shlUp (k : Nat) : Reg → List Reg → List Reg → List Instr
  | b, d :: ds, s :: ss => shlUp k s ds ss ++ [.extr .x d s b (64 - k)]
  | b, d :: _, [] => [.lsr .x d b (64 - k)]
  | _, [], _ => []

/-- `ds = 2^k ss`. -/
def shl (k : Nat) : List Reg → List Reg → List Instr
  | d :: ds, s :: ss => shlUp k s ds ss ++ [.lsl .x d s k]
  | _, _ => []

/-- `A` and `p - B`, and `x7 = 0`. -/
def operands (a b : Nat) : List Instr :=
  zero7 :: loads aw a ++ loads bw b ++ loads sw M.mo ++ P384Field.subs true bw sw bw

/-- `sw + x14 2^384 += xs`. -/
def more (xs : List Reg) : List Instr :=
  P384Field.adds true sw sw xs ++ ([.adc .x .x14 .x14 .x7] : List Instr)

/-- `sw + x14 2^384 = xs + ys`. -/
def sum (xs ys : List Reg) : List Instr :=
  P384Field.adds true sw xs ys ++ ([.adc .x .x14 .x7 .x7] : List Instr)

/-- `sw + x14 2^384` modulo `p`, below `2p`, for a small `x14`. -/
def fold : List Instr :=
  ([.lsl .x .x1 .x14 32, .sub .x .x2 .x1 .x14, .subs .x .x3 .x7 .x2, .sbc .x .x4 .x1 .x7] : List Instr) ++
    P384Field.adds true sw sw [.x3, .x4, .x14, .x7, .x7, .x7] ++ ([.adc .x .x14 .x7 .x7] : List Instr)

/-- The sum modulo `p`, stored. -/
def finish (o : Nat) : List Instr := fold ++ csubR M sw .x14 ++ stores sw o

/-- `[o] = 9 [a] - 8 [b]`. -/
def lin98 (o a b : Nat) : List Instr :=
  operands a b ++ sum aw bw ++ shl 3 (sw ++ [.x14]) (sw ++ [.x14]) ++ more aw ++ finish o

/-- `[o] = 4 [a] - [b]`. -/
def lin41 (o a b : Nat) : List Instr :=
  operands a b ++ shl 2 (sw ++ [.x14]) aw ++ more bw ++ finish o

/-- `[o] = 3 [a] - 8 [b]`. -/
def lin38 (o a b : Nat) : List Instr :=
  operands a b ++ shl 2 (sw ++ [.x14]) bw ++ more aw ++ shl 1 (sw ++ [.x14]) (sw ++ [.x14]) ++ more aw ++ finish o

end VG.Impl.P384.Linear
