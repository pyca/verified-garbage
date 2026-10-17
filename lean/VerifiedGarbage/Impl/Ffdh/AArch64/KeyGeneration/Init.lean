module

public import VerifiedGarbage.Impl.Bignum.AArch64.Core

/-! # Native FFDH key generation on AArch64: validation and rejection budgets

`vg_ffdh_key_generation_init(state = x0, p_len = x1)`: `x13 := 1` exactly
when `64 ≤ p_len ≤ 1024`, by the carries of two subtractions; then both
budgets 128, the width and the first request `p_len`, and 1 returned, or
zeros to the four public words and 0 returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.AArch64.KeyGeneration

open VG VG.AArch64 VG.Impl.Bignum.AArch64

/-- `x13 := 64 ≤ p_len ∧ p_len < 1025`, as 1 or 0. -/
def validate : List Instr := [
  movi .x9 64, movi .x11 0, movi .x12 1, .subs .x .x10 .x1 .x9, .csel .x .x13 .x12 .x11,
  movi .x9 1025, .subs .x .x10 .x1 .x9, .csel .x .x14 .x11 .x12, .logic .and .x .x13 .x13 .x14]

/-- Zeros to the four public words, and 0 returned. -/
def clear : List Instr := [
  movi .x9 0, st .x9 .x0 0, st .x9 .x0 8, st .x9 .x0 16, st .x9 .x0 24, movi .x0 0]

/-- Both budgets 128, the width and the first request `p_len`, and 1 returned. -/
def initializeState : List Instr := [
  movi .x9 128, st .x9 .x0 0, st .x9 .x0 8, st .x1 .x0 16, st .x1 .x0 24, movi .x0 1]

def init : Prog isa := .seq (.block validate) (.ite (.zero .x .x13) (.block clear) (.block initializeState))

end VG.Impl.Ffdh.AArch64.KeyGeneration
