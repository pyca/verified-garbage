module

public import VerifiedGarbage.TCB.RISCV64.Isa

/-! # Native FFDH parameter generation on RISC-V: validation and limits

`vg_ffdh_parameter_generation_init(state = a0, bits = a1, generator = a2)`.
The generator's low word is first zero-extended into `a2` (the ABI passes a
`u32` sign-extended); then, by unsigned comparisons with `sltu`, `t0 := 0`
exactly when `512 ≤ bits ≤ 8192` and the generator is 2 or 5 (`g == c` as
`(g < c + 1) − (g < c)`), a branch on public values. Then the attempt limit
`bits² · 64`, the width `⌈bits / 8⌉`, the entropy cap `32769 ⌈bits / 8⌉` and
the first request `512 ⌈bits / 8⌉`, and 1 returned, or zeros to the four
public words and 0 returned.
-/

@[expose] public section

namespace VG.Impl.Ffdh.RISCV64.Generation

open VG.RISCV64

/-- `a2 :=` the generator's low word, zero-extended. -/
def zext : List Instr := [.shift .sll .d .a2 .a2 32, .shift .srl .d .a2 .a2 32]

/-- `d := 1` if `n < c`, else 0, for `c < 2048` (`t2` scratch). -/
def lt (d n : Reg) (c : Nat) : List Instr := [.li .t2 c, .sltu d n .t2]

/-- `t0 :=` 0 exactly when `512 ≤ bits ≤ 8192` and the generator, in `a2`,
is 2 or 5. -/
def validate : List Instr :=
  lt .t0 .a1 512 ++ [.lui .t2 2, .sltu .t1 .t2 .a1, .logic .or .t0 .t0 .t1] ++
  lt .t1 .a2 2 ++ lt .t3 .a2 3 ++ [.sub .t1 .t3 .t1] ++
  lt .t3 .a2 5 ++ lt .t4 .a2 6 ++ [.sub .t3 .t4 .t3, .logic .or .t1 .t1 .t3,
    .logicImm .xor .t1 .t1 1, .logic .or .t0 .t0 .t1]

/-- The four public words, and 1 returned. -/
def initializeState : List Instr := [
  .mul .t0 .a1 .a1, .shift .sll .d .t0 .t0 6, .addi .t1 .a1 7, .shift .srl .d .t1 .t1 3,
  .shift .sll .d .t2 .t1 15, .add .t2 .t2 .t1, .shift .sll .d .t3 .t1 9,
  .store .d .t0 .a0 0, .store .d .t1 .a0 8, .store .d .t2 .a0 16, .store .d .t3 .a0 24, .li .a0 1]

/-- Zeros to the four public words, and 0 returned. -/
def clear : List Instr :=
  [.li .t2 0, .store .d .t2 .a0 0, .store .d .t2 .a0 8, .store .d .t2 .a0 16, .store .d .t2 .a0 24, .li .a0 0]

/-- After `zext`. -/
def rest : Prog isa :=
  .seq (.block validate) (.ite (.zero .t0) (.block initializeState) (.block clear))

/-- `vg_ffdh_parameter_generation_init`. -/
def init : Prog isa := .seq (.block zext) rest

end VG.Impl.Ffdh.RISCV64.Generation
