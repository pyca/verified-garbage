module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# Division by words for the RSA key operations on RISC-V

`divW a r m t`: `[r] := [a] mod [m]` for a divisor of `w / 2` words (the
working space's numbers are `w` words, `w` even), by long division a word at
a time (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D), with
`vg_rsa_public_precompute`'s word step (`Precompute.wordStepU`):
`[r] := ([r] 2^64 + u) mod [m]` for each of `[a]`'s `w` words `u`, most
significant first, from `[r] = 0`, as on PPC64LE
(`Impl/Rsa/PPC64LE/KeyDiv.lean`).

The step needs the divisor normalized: `z`, the leading zeros of its top word
(`Precompute.lz`, 63 steps whatever the word), then `P = 2^z`, `d'` and
`d'ₗ`, the top two words of `[m] P` (`Precompute.normTail`), and the
reciprocal `v` of `d'` by restoring division (`Precompute.recip`), all in the
temporary `[t]`. A divisor whose top word is zero has it set to 1 first
(`fixTop`), so that the step's precondition always holds; the remainder is
then exact for a divisor whose top word is not zero.

`[r]` is zeroed by the caller. Then `a7` holds `[m]`'s address, `a6` `[t]`'s,
`a2` `[r]`'s, `t0` `w / 2`, `t2` the address of the word `u` and `a1` the
steps left. Every address and count depends only on `w` and the base: none on
the numbers. The registers written are the argument registers, `t0`–`t6` and
`s0`–`s4`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.WordDiv

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys
open VG.Impl.Bignum.RISCV64.Precompute (lz normTail recip wordStepU)

/-- `t0 := w / 2`, the divisor's words. -/
def halfW : Instr := .shift .srl .d .t0 .s9 1

/-- `[m]`'s top word (`w / 2 - 1`) plus 1 if it is zero, so that it never is:
the divisor is unchanged unless its top word is zero. -/
def fixTop (m : Nat) : List Instr :=
  ptr .a7 m ++ [halfW, .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t5 .t3 0,
    .li .t6 1, .sltu .t6 .t5 .t6, .add .t5 .t5 .t6, .store .d .t5 .t3 0]

/-- `a7 :=` `[m]`'s address, `a6 :=` `[t]`'s, `t0 := w / 2`. -/
def normSetup (m t : Nat) : List Instr := ptr .a7 m ++ ptr .a6 t ++ [halfW]

/-- `a2 :=` `[r]`'s address, `t2 :=` the address of `[a]`'s top word
(`w - 1`), `a1 := w` steps. -/
def stepsSetup (a r : Nat) : List Instr :=
  ptr .a2 r ++ ptr .t2 a ++ [.shift .sll .d .t3 .s9 3, .add .t2 .t2 .t3, .addi .t2 .t2 (-8), .addi .a1 .s9 0]

/-- A step, then `u`'s address a word down and a step less. -/
def step : Prog isa := .seq wordStepU (.block [.addi .t2 .t2 (-8), .addi .a1 .a1 (-1)])

/-- The divisor normalized and its reciprocal, in the temporary. -/
def prep (m t : Nat) : Prog isa := seqs [.block (normSetup m t), lz, .block normTail, recip]

/-- `[r] := [a] mod [m]`, for `[r]` zero and `[m]`'s top word not zero,
through `[t]`. -/
def divW (a r m t : Nat) : Prog isa := seqs [prep m t, .block (stepsSetup a r), .loop step (.nonzero .a1)]

end VG.Impl.Rsa.RISCV64.WordDiv
