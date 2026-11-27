module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # Native FFDH key generation on RISC-V: validation and rejection budgets

`vg_ffdh_key_generation_init(state = a0, p_len = a1)`: `t0 := (p_len < 64) |
(1024 < p_len)` by unsigned comparisons, zero exactly when
`64 ≤ p_len ≤ 1024`, a branch on a public value; then both budgets 128, the
width and the first request `p_len`, and 1 returned, or zeros to the four
public words and 0 returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.KeyGeneration

open VG.RISCV64

/-- `t0 :=` 0 exactly when `64 ≤ p_len ≤ 1024`. -/
def validate : List Instr :=
  [.li .t2 64, .sltu .t0 .a1 .t2, .li .t2 1024, .sltu .t1 .t2 .a1, .logic .or .t0 .t0 .t1]

/-- Both budgets 128, the width and the first request `p_len`, and 1
returned. -/
def initializeState : List Instr :=
  [.li .t2 128, .store .d .t2 .a0 0, .store .d .t2 .a0 8, .store .d .a1 .a0 16, .store .d .a1 .a0 24, .li .a0 1]

/-- Zeros to the four public words, and 0 returned. -/
def clear : List Instr :=
  [.li .t2 0, .store .d .t2 .a0 0, .store .d .t2 .a0 8, .store .d .t2 .a0 16, .store .d .t2 .a0 24, .li .a0 0]

/-- `vg_ffdh_key_generation_init`. -/
def init : Prog isa :=
  .seq (.block validate) (.ite (.zero .t0) (.block initializeState) (.block clear))

end VG.Impl.Ffdh.RISCV64.KeyGeneration
