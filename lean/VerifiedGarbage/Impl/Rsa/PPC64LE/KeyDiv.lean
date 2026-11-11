module

public import VerifiedGarbage.Impl.Rsa.PPC64LE.KeyWs
public import VerifiedGarbage.Impl.Bignum.PPC64LE.Precompute

/-!
# Division by words for the RSA key checks on PPC64LE

`divW a r m t sv`: `[r] := [a] mod [m]` for a divisor of `wd = w / 4` words
of 64 bits (`w` digits of 32 bits for the working space's numbers, a
multiple of 4), by long division a word at a time (Knuth, TAOCP vol. 2,
§4.3.1, Algorithm D), with `vg_rsa_public_precompute`'s word step
(`Precompute.wordStepU`): `[r] := ([r] 2^64 + u) mod [m]` for each of
`[a]`'s `w / 2` words `u`, most significant first, from `[r] = 0`.

The step needs the divisor's top word at least `2^63`: its top bit is set
first (`force`), which changes nothing for the divisors the key checks need
it for, `p - 1` and `q - 1` of a balanced key (`p q = n` with `n`'s top bit
set and `p`, `q` of half its length). Then `P = 1`, `d'` and `d'ₗ` are the
divisor's top two words, and the reciprocal `v` of `d'` is computed by
restoring division (`Precompute.recip`), all in the temporary `[t]`.

The step uses the nonvolatile `r14`–`r18`, `r20` and `r22`, saved in the
array `sv` and restored. `[r]`'s `w` digits are zeroed first
(`Precompute.zeroWords`). Then `r5` holds `[r]`'s address, `r10` `[m]`'s,
`r9` `[t]`'s, `r11` `w / 2`, `r8` the address of the word `u` and `r4` the
steps left. Every address and count depends only on `w` and the base: none on
the numbers.
-/

@[expose] public section

namespace VG.Impl.Rsa.PPC64LE.KeyDiv

open VG.PPC64LE VG.Impl.Rsa.PPC64LE.Keys
open VG.Impl.Bignum.PPC64LE.Precompute (recip wordStepU zeroWords)

/-- `r14`–`r18`, `r20` and `r22` into the array `sv`. -/
def save (sv : Nat) : List Instr :=
  ptr .r5 sv ++ [.store .d .r14 .r5 0, .store .d .r15 .r5 8, .store .d .r16 .r5 16, .store .d .r17 .r5 24,
    .store .d .r18 .r5 32, .store .d .r20 .r5 40, .store .d .r22 .r5 48]

/-- And back. -/
def restore (sv : Nat) : List Instr :=
  ptr .r5 sv ++ [.load .d .r14 .r5 0, .load .d .r15 .r5 8, .load .d .r16 .r5 16, .load .d .r17 .r5 24,
    .load .d .r18 .r5 32, .load .d .r20 .r5 40, .load .d .r22 .r5 48]

/-- `r11 := w / 2`, `[m]`'s top word (`wd - 1`) with its top bit set, and
the temporary: `P = 1`, `d'` the top word and `d'ₗ` the one below it. -/
def force (m t : Nat) : List Instr :=
  ptr .r10 m ++ ptr .r9 t ++ [.lsr .d .r11 .r29 1, .lsl .r14 .r11 2, .add .r14 .r14 .r10, .subi .r14 .r14 8,
    .load .d .r0 .r14 0, .li .r3 1, .lsl .r3 .r3 63, .logic .or .r0 .r0 .r3, .store .d .r0 .r14 0,
    .li .r3 1, .store .d .r3 .r9 0, .store .d .r0 .r9 8, .subi .r14 .r14 8, .load .d .r0 .r14 0,
    .store .d .r0 .r9 24]

/-- `r5 := [r]`'s address, `r8 :=` the address of `[a]`'s top word (`w / 2 -
1`), `r4 := w / 2` steps. -/
def stepsSetup (a r : Nat) : List Instr :=
  ptr .r5 r ++ ptr .r8 a ++ [.lsl .r0 .r11 3, .add .r8 .r8 .r0, .subi .r8 .r8 8, .addi .r4 .r11 0]

/-- A step, then `u`'s address a word down and a step less. -/
def step : Prog isa := .seq wordStepU (.block [.subi .r8 .r8 8, .subi .r4 .r4 1])

/-- The registers saved and `[r]` zeroed. -/
def prepA (r sv : Nat) : Prog isa :=
  seqs [.block (save sv), .block (ptr .r14 r ++ [.addi .r11 .r29 0]), zeroWords]

/-- The divisor and the temporary, and the steps' registers. -/
def prepB (a r m t : Nat) : Prog isa := seqs [.block (force m t), recip, .block (stepsSetup a r)]

/-- `[r] := [a] mod [m]`, `[m]`'s top bit set, through `[t]` and the save
area `sv`. -/
def divW (a r m t sv : Nat) : Prog isa := seqs [prepA r sv, prepB a r m t, .loop step (.nonzero .d .r4),
  .block (restore sv)]

end VG.Impl.Rsa.PPC64LE.KeyDiv
