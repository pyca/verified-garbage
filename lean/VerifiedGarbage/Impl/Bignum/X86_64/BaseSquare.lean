module

public import VerifiedGarbage.Impl.Bignum.X86_64.AdxSquare

/-!
# Montgomery squaring without BMI2 or ADX (x86-64)

`vg_rsa_mont_mul`'s path for `a = b`: the products `a_i a_j` for `i ≠ j` once
(`AdxSquare.crossWith`), doubled, with the squares `a_i²` added
(`AdxSquare.diagonalWith`), then a Montgomery reduction of the `2 w`-word
square, row by row (`redc`), and `montMul`'s final subtraction. About
`3 w² / 2` multiplications instead of `montMul`'s `2 w²`.

The rows are `mul`, `add` and `adc` (`row`, `core`, `head`). The square lies
at `aAcc + 16`, over arrays `aAcc` and `aTmp`, as in `AdxSquare`, and the
reduction leaves its result at `aTmp`. The code reads nothing from the
header: it keeps the bases of `o`, the accumulator, the temporary and `m`, `w`
and `-m⁻¹` in `xmm14`, `xmm1`, `xmm3`, `xmm2`, `xmm0` and `xmm15`.
-/

@[expose] public section

namespace VG.Impl.Bignum.X86_64.BaseSquare

open VG.X86_64 VG.Impl.Bignum.X86_64

/-- A multiply-add step at word `r14`: the low word of `r13 · [r9] + [r8] + rcx`
stored at `[r8]`, its high word into `rcx`. As in `mac`, the carry passes
through one addition. -/
def macR : List Instr :=
  [.mov .rax (.mem (ix .r9 .r14)), .mul .r13, .alu .add .rax (.mem (ix .r8 .r14)), .alu .adc .rdx (.imm 0),
    .alu .add .rax (.reg .rcx), .alu .adc .rdx (.imm 0), .store (ix .r8 .r14) .rax, .mov .rcx (.reg .rdx)]

/-- `macR`, then `r14 += 1` and the flags of `r14 = rbp`. -/
def macStep : List Instr := macR ++ ([.alu .add .r14 (.imm 1), .alu .cmp .r14 (.reg .rbp)] : List Instr)

/-- `[r8] += rdx · [r9]` over `rbp > 0` words, the carry word into `rcx`
(`AdxSquare.RowOk`): the multiplier is kept in `r13`, as `mul` writes `rdx`. -/
def row : Prog isa :=
  .seq (.block [.mov .r13 (.reg .rdx), .mov32 .rcx (.imm 0), .mov32 .r14 (.imm 0)])
    (.seq (.loop (.block macStep) .ne) (.block [.mov .rdx (.reg .r13)]))

/-- `rbx:r12:r11 = 2 (r11 + 2⁶⁴ r12) + rdx² + r15` (`AdxSquare.CoreOk`). -/
def core : List Instr :=
  [.mov .rax (.reg .rdx), .mov .rsi (.reg .rdx), .mul .rsi, .mov32 .rbx (.imm 0),
    .alu .add .r11 (.reg .r11), .alu .adc .r12 (.reg .r12), .alu .adc .rbx (.imm 0),
    .alu .add .r11 (.reg .rax), .alu .adc .r12 (.reg .rdx), .alu .adc .rbx (.imm 0),
    .alu .add .r11 (.reg .r15), .alu .adc .r12 (.imm 0), .alu .adc .rbx (.imm 0),
    .mov .rdx (.reg .rsi)]

/-- `rdx = [r8] · (-m⁻¹) mod 2⁶⁴`, `-m⁻¹` from `xmm15`. -/
def head : List Instr := [.movqR .rax .xmm15, .mov .rdx (.mem (at0 .r8)), .imul .rdx .rax]

/-- Reduction row `i`: `[r8] += u · m` over `w` words (`r9 = m`, `rbp = w`)
for the `u` that cancels `[r8]`, the carry added to word `w` with the
pending carry `r10` (`AdxSquare.redcTail`, which moves `r8` up a word), and
the flags of `r8` reaching the temporary (`xmm3`). -/
def redcRow : Prog isa :=
  .seq (.block head) (.seq row (.seq (.block AdxSquare.redcTail) (.block [.movqR .rax .xmm3, .alu .cmp .r8 (.reg .rax)])))

/-- The square at `aAcc + 16` (`r8`, left there by the diagonal) reduced into
`aTmp`, with its pending carry and a zero word above. -/
def redc : Prog isa :=
  .seq (.block [.movqR .r9 .xmm2, .movqR .rbp .xmm0, .mov32 .r10 (.imm 0)])
    (.seq (.loop redcRow .ne) (.block AdxSquare.redcFinish))

/-- The bases (`rbx`, `r8`, `rsi`, `r10`), `w` (`r12`) and `-m⁻¹` (`r15`)
from `basesR` into the vector registers. -/
def stash : List Instr :=
  [.xop (.movq .xmm14 .rbx), .xop (.movq .xmm15 .r15), .xop (.movq .xmm0 .r12), .xop (.movq .xmm1 .r8),
    .xop (.movq .xmm2 .r10), .xop (.movq .xmm3 .rsi)]

/-- `[a]²` (`[a]` at `r9`) at `aAcc + 16`, over `2 w` words, from `basesR`'s
registers, which it stashes. -/
def raw : Prog isa :=
  .seq (.block (stash ++ ([.mov .rbx (.reg .r12), .alu .add .r8 (.imm 16)] : List Instr)))
    (.seq (AdxSquare.crossWith row)
    (.seq (.block [.movqR .r8 .xmm1, .alu .add .r8 (.imm 16), .movqR .r10 .xmm0])
      (AdxSquare.diagonalWith core)))

/-- The registers of `subMod` and `selectAcc` back from the stash, for the
reduction's result at `aTmp` (in `r8`). -/
def unstash : List Instr := [.movqR .r12 .xmm0, .movqR .rsi .xmm1, .movqR .r10 .xmm2, .movqR .rbx .xmm14]

/-- `[o] = [a]² R⁻¹ mod m` from `basesR`'s registers, for `[a]` at `r9`. -/
def square : Prog isa :=
  .seq raw (.seq redc (.seq (.block unstash) (.seq subMod selectAcc)))

/-- What follows `basesR` in `vg_rsa_mont_mul`: `square` if `a` and `b` are
the same array, `montMul`'s rounds otherwise. -/
def mulTail : Prog isa :=
  .seq (.block [.alu .cmp .r11 (.reg .r9)])
    (.ite .e square (.seq zeroAccLoop (.seq rounds (.seq subMod selectAcc))))

end VG.Impl.Bignum.X86_64.BaseSquare
