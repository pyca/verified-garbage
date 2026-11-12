module

public import VerifiedGarbage.Impl.Rsa.RISCV64.KeyWs
public import VerifiedGarbage.Impl.Bignum.RISCV64.Precompute

/-!
# Division by words for the RSA key operations on RISC-V

`divCore a r m t q`: `[r] := [a] mod [m]`, and with `q = some (dig, q)`
`[q] := ⌊[a] / [m]⌋`, for a divisor of `v` words (`t0`) and a dividend of
`Wd` words (`t6`), by long division of `X = [a]` 63 bits at a time (Knuth,
TAOCP vol. 2, §4.3.1, Algorithm D), with `vg_rsa_public_precompute`'s step
(`Precompute.step`), whose remainder is kept lazily in `[0, 2 [m])` and
reduced once at the end (`Precompute.finish`). `divW a r m t` is the
remainder alone for the working space's `w`-word dividend and `w / 2`-word
divisor.

The step needs the divisor normalized: `z`, the leading zeros of its top word
(`Precompute.lz`, 63 steps whatever the word), then `P = 2^z`, `d'` and
`d'ₗ`, the top two words of `[m] P` (`Precompute.normTail`), and the
reciprocal `v` of `d'` by restoring division (`Precompute.recip`), all in the
temporary `[t]`. A divisor whose top word is zero has it set to 1 first
(`fixTop`), so that the step's precondition always holds; the remainder is
then exact for a divisor whose top word is not zero.

The number `V` of a step is `v + 1` words in `[r]`. It starts at
`⌊X / 2^(63 (S - 1))⌋` for `S = Y + c` steps, `Y = Wd - v + 1` and
`c = ⌈Y / 63⌉` (`stepCount`), which is below `2^(64 (v - 1) + 63)` and so a
valid first `V` for any divisor (`divInit`, a copy of `X`'s top words
shifted down); each step then takes the next 63-bit chunk of `X`, most
significant first (`chunk`, at the bit offset in `t1`), the last a dummy
that `finish` drops. As the first `v - 1` words of `X` are below the
divisor, this is `v - 1` steps of 64 bits fewer than dividing from zero.

The quotient: step `j` stores its digit `q̂` (`storeQ`) at word `j` of
`[dig]`, of weight `2^(63 (S - 1 - j))`, and `finish` leaves `g = 1` in its
mask where it subtracted the divisor once more. `combine` adds the digits
from the least significant, with `g`, carrying between them, and writes each
63-bit digit of the sum into `[q]` at bit `63 k`.

`[r]` and `[q]` are zeroed by the caller. Then `a7` holds `[m]`'s address,
`a6` `[t]`'s, `a2` `[r]`'s, `a5` `[a]`'s, `t0` `v`, `t1` the chunk's bit
offset, `a1` the steps left, and with a quotient `t2` the next digit's
address, `s7` `S` and `s8` `[dig]`'s address. Every address and count
depends only on `v`, `Wd`, `w` and the base: none on the numbers. The
registers written are the argument registers, `t0`–`t6` and `s0`–`s4`, and
with a quotient `s7` and `s8`.
-/
@[expose] public section

namespace VG.Impl.Rsa.RISCV64.WordDiv

open VG.RISCV64 VG.Impl.Rsa.RISCV64.Keys
open VG.Impl.Bignum.RISCV64 (countLoop)
open VG.Impl.Bignum.RISCV64.Precompute (lz normTail recip step finish)

/-- `t0 := w / 2`, the divisor's words. -/
def halfW : Instr := .shift .srl .d .t0 .s9 1

/-- `[m]`'s top word (`w / 2 - 1`) plus 1 if it is zero, so that it never is:
the divisor is unchanged unless its top word is zero. -/
def fixTop (m : Nat) : List Instr :=
  ptr .a7 m ++ [halfW, .shift .sll .d .t3 .t0 3, .add .t3 .t3 .a7, .addi .t3 .t3 (-8), .load .d .t5 .t3 0,
    .li .t6 1, .sltu .t6 .t5 .t6, .add .t5 .t5 .t6, .store .d .t5 .t3 0]

/-- `a7 :=` `[m]`'s address, `a6 :=` `[t]`'s. -/
def normSetup (m t : Nat) : List Instr := ptr .a7 m ++ ptr .a6 t

/-- The divisor normalized and its reciprocal, in the temporary. -/
def prep (m t : Nat) : Prog isa := seqs [.block (normSetup m t), lz, .block normTail, recip]

/-- From `t6 = Wd` and `t0 = v`: `Y = Wd - v + 1` (`s4`), `c = ⌈Y / 63⌉ =
1 + [Y > 63] + [Y > 126]` (`s0`, for `Y < 189`) and the steps `S = Y + c`
(`a1`). -/
def stepCount : List Instr :=
  [.sub .s4 .t6 .t0, .addi .s4 .s4 1, .li .s0 63, .sltu .s0 .s0 .s4, .li .s1 126, .sltu .s1 .s1 .s4,
    .add .s0 .s0 .s1, .addi .s0 .s0 1, .add .a1 .s4 .s0]

/-- `a5 :=` `[a]`'s address, `a2 :=` `[r]`'s, the steps `S` (`a1`), the first
chunk's offset `o = 63 (S - 1)` (`t1`), and for the copy of `⌊X / 2^o⌋`:
the address of `X`'s word `J = ⌊o / 64⌋` (`t3`), `[r]`'s (`t4`), the words
`Wd - J - 1` (`t5`) and the shifts `o mod 64` (`s3`) and `63 - o mod 64`
(`a3`). -/
def divSetup (a r : Nat) : List Instr :=
  ptr .a5 a ++ ptr .a2 r ++ stepCount ++
    [.addi .t1 .a1 (-1), .shift .sll .d .s1 .t1 6, .sub .t1 .s1 .t1, .shift .srl .d .s2 .t1 6,
      .shift .sll .d .t3 .s2 3, .add .t3 .t3 .a5, .addi .t4 .a2 0, .sub .t5 .t6 .s2, .addi .t5 .t5 (-1),
      .logicImm .and .s3 .t1 63, .logicImm .xor .a3 .s3 63]

/-- A word of the copy: `⌊(X_{j+1} 2^64 + X_j) / 2^(o mod 64)⌋ mod 2^64`. -/
def copyWord : List Instr :=
  [.load .d .s0 .t3 0, .load .d .s2 .t3 8, .shiftReg .srl .d .s0 .s0 .s3, .shift .sll .d .s2 .s2 1,
    .shiftReg .sll .d .s2 .s2 .a3, .logic .or .s0 .s0 .s2, .store .d .s0 .t4 0, .addi .t3 .t3 8,
    .addi .t4 .t4 8]

/-- `V := ⌊X / 2^o⌋` into `[r]`'s first `Wd - J` words, after `divSetup`. -/
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

/-- The `S` steps, each with `mid` and then `post`, counted by `a1`. -/
def steps (mid post : List Instr) : Prog isa :=
  .loop (.seq (step mid) (.block (post ++ [.addi .a1 .a1 (-1)]))) (.nonzero .a1)

/-- After a step, its digit `q̂` (`s1`) stored at `t2`, the next digit's address after. -/
def storeQ : List Instr := [.store .d .s1 .t2 0, .addi .t2 .t2 8]

/-- `t2 :=` `[dig]`'s address, and it (`s8`) and `S` (`s7`) kept for `combine`. -/
def digInit (dig : Nat) : List Instr := ptr .t2 dig ++ [.addi .s7 .a1 0, .addi .s8 .t2 0]

/-- One digit of the sum, from the least significant: the digit `q = h 2^63 + l`
(at `t2`), `e = l + h' + c` for the previous `h'` (`s1`) and carry `c` (`s0`),
the new carry `⌊e / 2^63⌋`, and `e mod 2^63` or-ed into `[q]` (at `a2`) at bit
`t1`: into its word `⌊t1 / 64⌋` shifted up by `t1 mod 64`, and the next word
by what is left. -/
def combBody : List Instr :=
  [.load .d .t3 .t2 0, .shift .srl .d .t4 .t3 63, .shift .sll .d .t3 .t3 1, .shift .srl .d .t3 .t3 1,
    .add .t3 .t3 .s1, .add .t3 .t3 .s0, .shift .srl .d .s0 .t3 63, .shift .sll .d .t3 .t3 1,
    .shift .srl .d .t3 .t3 1, .addi .s1 .t4 0,
    .shift .srl .d .t5 .t1 6, .shift .sll .d .t5 .t5 3, .add .t5 .t5 .a2, .logicImm .and .t6 .t1 63,
    .load .d .a0 .t5 0, .shiftReg .sll .d .a3 .t3 .t6, .logic .or .a0 .a0 .a3, .store .d .a0 .t5 0,
    .load .d .a0 .t5 8, .shift .srl .d .a3 .t3 1, .logicImm .xor .t6 .t6 63, .shiftReg .srl .d .a3 .a3 .t6,
    .logic .or .a0 .a0 .a3, .store .d .a0 .t5 8, .addi .t1 .t1 63, .addi .t2 .t2 (-8)]

/-- The quotient into `[q]` (zero): the `S` digits (`s7`) at `s8`, from the
last, and `g`, the low bit of `finish`'s mask `s1 = 0 - g`, as the first carry. -/
def combine (q : Nat) : Prog isa :=
  .seq (.block (ptr .a2 q ++ [.logicImm .and .s0 .s1 1, .li .s1 0, .shift .sll .d .t2 .s7 3, .add .t2 .t2 .s8,
      .addi .t2 .t2 (-8), .li .t1 0, .addi .a1 .s7 0]))
    (countLoop .a1 combBody)

/-- `[r] := [a] mod [m]`, and with `some (dig, q)` `[q] := ⌊[a] / [m]⌋` (its
digits in `[dig]`), for `t0 = v` the divisor's words, its top word not zero,
`t6 = Wd` the dividend's, `[r]` and `[q]` zero, through `[t]`. -/
def divCore (a r m t : Nat) : Option (Nat × Nat) → Prog isa
  | none => seqs [prep m t, divInit a r, steps chunk [], finish]
  | some (dig, q) => seqs [prep m t, divInit a r, .block (digInit dig), steps chunk storeQ, finish, combine q]

/-- `[r] := [a] mod [m]` for the working space's numbers, `w` words and a
divisor of `w / 2`, for `[r]` zero and `[m]`'s top word not zero, through
`[t]`. -/
def divW (a r m t : Nat) : Prog isa := .seq (.block [halfW, .addi .t6 .s9 0]) (divCore a r m t none)

end VG.Impl.Rsa.RISCV64.WordDiv
