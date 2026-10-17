module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Native FFDH parameter generation on AArch64: validation and limits

`vg_ffdh_parameter_generation_init(state = x0, bits = x1, generator = w2)`:
`x13 := 1` exactly when `512 ≤ bits ≤ 8192` and the generator is 2 or 5,
each bound by the carry of a subtraction made 0 or 1 by `csel`; then the
attempt limit `bits² · 64`, the width `⌈bits / 8⌉`, the entropy cap
`32769 ⌈bits / 8⌉` and the first request `512 ⌈bits / 8⌉`, and 1 returned,
or zeros to the four public words and 0 returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.Generation

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- `x13 := 512 ≤ bits < 8193`, and the generator, zero-extended into `x2`,
2 (`2 ≤ g < 3`) or 5 (`5 ≤ g < 6`), as 1 or 0. -/
def validate : List Instr := [
  movi .x11 0, movi .x12 1, movi .x9 512, .subs .x .x10 .x1 .x9, .csel .x .x13 .x12 .x11,
  movi .x9 8193, .subs .x .x10 .x1 .x9, .csel .x .x14 .x11 .x12, .logic .and .x .x13 .x13 .x14,
  .addImm .w .x2 .x2 0,
  movi .x9 2, .subs .x .x10 .x2 .x9, .csel .x .x15 .x12 .x11,
  movi .x9 3, .subs .x .x10 .x2 .x9, .csel .x .x16 .x11 .x12, .logic .and .x .x15 .x15 .x16,
  movi .x9 5, .subs .x .x10 .x2 .x9, .csel .x .x16 .x12 .x11,
  movi .x9 6, .subs .x .x10 .x2 .x9, .csel .x .x17 .x11 .x12, .logic .and .x .x16 .x16 .x17,
  .logic .orr .x .x15 .x15 .x16, .logic .and .x .x13 .x13 .x15]

/-- Zeros to the four public words, and 0 returned. -/
def clear : List Instr := [
  movi .x9 0, st .x9 .x0 0, st .x9 .x0 8, st .x9 .x0 16, st .x9 .x0 24, movi .x0 0]

/-- The four public words, and 1 returned. -/
def initializeState : List Instr := [
  .mul .x .x9 .x1 .x1, .lsl .x .x9 .x9 6, .addImm .x .x10 .x1 7, .lsr .x .x10 .x10 3,
  .lsl .x .x11 .x10 15, .add .x .x11 .x11 .x10, .lsl .x .x12 .x10 9,
  st .x9 .x0 0, st .x10 .x0 8, st .x11 .x0 16, st .x12 .x0 24, movi .x0 1]

def init : Prog isa := .seq (.block validate) (.ite (.zero .x .x13) (.block clear) (.block initializeState))

end VG.Impl.Ffdh.AArch64.Generation
