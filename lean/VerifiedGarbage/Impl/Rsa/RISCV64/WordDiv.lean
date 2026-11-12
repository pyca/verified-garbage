module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# Division by words for the RSA key operations on RISC-V

`divW a r m t`: `[r] := [a] mod [m]` for a divisor of `v = w / 2` words (the
working space's numbers are `w` words, `w` even), by long division of
`X = [a]` 63 bits at a time (Knuth, TAOCP vol. 2, §4.3.1, Algorithm D), with
`vg_rsa_public_precompute`'s step (`Precompute.step`), whose remainder is
kept lazily in `[0, 2 [m])` and reduced once at the end (`Precompute.finish`).

The step needs the divisor normalized: `z`, the leading zeros of its top word
(`Precompute.lz`, 63 steps whatever the word), then `P = 2^z`, `d'` and
`d'ₗ`, the top two words of `[m] P` (`Precompute.normTail`), and the
reciprocal `v` of `d'` by restoring division (`Precompute.recip`), all in the
temporary `[t]`. A divisor whose top word is zero has it set to 1 first
(`fixTop`), so that the step's precondition always holds; the remainder is
then exact for a divisor whose top word is not zero.

The number `V` of a step is `v + 1` words in `[r]`. It starts at
`⌊X / 2^(63 (S - 1))⌋` for `S = v + 1 + c` steps, `c = ⌈(v + 1) / 63⌉`
(`Precompute.stepCount`), which is below `2^(64 (v - 1) + 63)` and so a
valid first `V` for any divisor (`divInit`, a copy of `X`'s top words
shifted down); each step then takes the next 63-bit chunk of `X`, most
significant first (`chunk`, at the bit offset in `t1`), the last a dummy
that `finish` drops. As the first `v - 1` words of `X` are below the
divisor, this is `v - 1` steps of 64 bits fewer than dividing from zero.

`[r]` is zeroed by the caller. Then `a7` holds `[m]`'s address, `a6` `[t]`'s,
`a2` `[r]`'s, `a5` `[a]`'s, `t0` `v`, `t1` the chunk's bit offset and `a1`
the steps left. Every address and count depends only on `w` and the base:
none on the numbers. The registers written are the argument registers,
`t0`–`t6` and `s0`–`s4`.
-/

@[expose] public section

namespace VG.Impl.Rsa.RISCV64.WordDiv

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.Bignum.RISCV64.Precompute (lz normTail recip step stepCount finish)

/-- `t0 := w / 2`, the divisor's words. -/
def halfW : Instr := .shift .srl .d .t0 .s9 1

/-- `[m]`'s top word (`w / 2 - 1`) plus 1 if it is zero, so that it never is:
the divisor is unchanged unless its top word is zero. -/
def fixTop (m : Nat) : List Instr :=
  ptr .a7 m ++ [halfW, .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t5 .t3 0,
    .li .t6 1, .sltu .t6 .t5 .t6, .add .t5 .t5 .t6, .store .d .t5 .t3 0]

/-- `a7 :=` `[m]`'s address, `a6 :=` `[t]`'s, `t0 := w / 2`. -/
def normSetup (m t : Nat) : List Instr := ptr .a7 m ++ ptr .a6 t ++ [halfW]

/-- The divisor normalized and its reciprocal, in the temporary. -/
def prep (m t : Nat) : Prog isa := seqs [.block (normSetup m t), lz, .block normTail, recip]

/-- `a5 :=` `[a]`'s address, `a2 :=` `[r]`'s, the steps `S` (`a1`), the first
chunk's offset `o = 63 (S - 1)` (`t1`), and for the copy of `⌊X / 2^o⌋`:
the address of `X`'s word `J = ⌊o / 64⌋` (`t3`), `[r]`'s (`t4`), the words
`w - J - 1` (`t5`) and the shifts `o mod 64` (`s3`) and `63 - o mod 64`
(`a3`). -/
def divSetup (a r : Nat) : List Instr :=
  ptr .a5 a ++ ptr .a2 r ++ stepCount ++
    [.addi .t1 .a1 (-1), .shift .sll .d .s1 .t1 6, .sub .t1 .s1 .t1, .shift .srl .d .s2 .t1 6,
      .shift .sll .d .t3 .s2 3, .add .t3 .t3 .a5, .addi .t4 .a2 0, .sub .t5 .s9 .s2, .addi .t5 .t5 (-1),
      .logicImm .and .s3 .t1 63, .logicImm .xor .a3 .s3 63]

/-- A word of the copy: `⌊(X_{j+1} 2^64 + X_j) / 2^(o mod 64)⌋ mod 2^64`. -/
def copyWord : List Instr :=
  [.load .d .s0 .t3 0, .load .d .s2 .t3 8, .shiftReg .srl .d .s0 .s0 .s3, .shift .sll .d .s2 .s2 1,
    .shiftReg .sll .d .s2 .s2 .a3, .logic .or .s0 .s0 .s2, .store .d .s0 .t4 0, .addi .t3 .t3 8,
    .addi .t4 .t4 8]

/-- `V := ⌊X / 2^o⌋` into `[r]`'s first `w - J` words, after `divSetup`. -/
def divInit (a r : Nat) : Prog isa :=
  .seq (.block (divSetup a r)) (.seq (countLoop .t5 copyWord)
    (.block [.load .d .s0 .t3 0, .shiftReg .srl .d .s0 .s0 .s3, .store .d .s0 .t4 0]))

/-- The next chunk's offset `o := max(o - 63, 0)` (`t1`), and `t6 :=` the 64
bits of `X` from bit `o` (words `⌊o / 64⌋` and the next), shifted up a bit:
`t6 / 2` is the 63-bit chunk at `o`. -/
def chunk : List Instr :=
  [.addi .t1 .t1 (-63), .shift .sra .d .t3 .t1 63, .logicImm .xor .t3 .t3 (-1), .logic .and .t1 .t1 .t3,
    .shift .srl .d .t3 .t1 6, .shift .sll .d .t3 .t3 3, .add .t3 .t3 .a5, .load .d .t4 .t3 0, .load .d .t5 .t3 8,
    .logicImm .and .a0 .t1 63, .shiftReg .srl .d .t4 .t4 .a0, .shift .sll .d .t5 .t5 1,
    .logicImm .xor .a0 .a0 63, .shiftReg .sll .d .t5 .t5 .a0, .logic .or .t4 .t4 .t5, .shift .sll .d .t6 .t4 1]

/-- The `S` steps, each with the next chunk, counted by `a1`. -/
def divSteps : Prog isa := .loop (.seq (step chunk) (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)

/-- `[r] := [a] mod [m]`, for `[r]` zero and `[m]`'s top word not zero,
through `[t]`. -/
def divW (a r m t : Nat) : Prog isa := seqs [prep m t, divInit a r, divSteps, finish]

end VG.Impl.Rsa.RISCV64.WordDiv
