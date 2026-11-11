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

The step needs the divisor normalized: `P = 2^z`, `d'` and `d'ₗ`, the top two
words of `[m] P`, are computed for any top word that is not zero
(`Precompute.norm`, by masks), then the reciprocal `v` of `d'` by restoring
division (`Precompute.recip`), all in the temporary `[t]`. Both run a fixed
number of steps, whatever the divisor.

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
open VG.Impl.Bignum.PPC64LE.Precompute (norm recip wordStepU zeroWords)

/-- `r14`–`r18`, `r20` and `r22` into the array `sv`. -/
def save (sv : Nat) : List Instr :=
  ptr .r5 sv ++ [.store .d .r14 .r5 0, .store .d .r15 .r5 8, .store .d .r16 .r5 16, .store .d .r17 .r5 24,
    .store .d .r18 .r5 32, .store .d .r20 .r5 40, .store .d .r22 .r5 48]

/-- And back. -/
def restore (sv : Nat) : List Instr :=
  ptr .r5 sv ++ [.load .d .r14 .r5 0, .load .d .r15 .r5 8, .load .d .r16 .r5 16, .load .d .r17 .r5 24,
    .load .d .r18 .r5 32, .load .d .r20 .r5 40, .load .d .r22 .r5 48]

/-- `r10 :=` `[m]`'s address, `r9 :=` `[t]`'s, `r11 := w / 2`. -/
def normSetup (m t : Nat) : List Instr := ptr .r10 m ++ ptr .r9 t ++ [.lsr .d .r11 .r29 1]

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
def prepB (a r m t : Nat) : Prog isa := seqs [.block (normSetup m t), norm, recip, .block (stepsSetup a r)]

/-- `[r] := [a] mod [m]`, for `[m]`'s top word not zero, through `[t]` and the
save area `sv`. -/
def divW (a r m t sv : Nat) : Prog isa := seqs [prepA r sv, prepB a r m t, .loop step (.nonzero .d .r4),
  .block (restore sv)]

end VG.Impl.Rsa.PPC64LE.KeyDiv
