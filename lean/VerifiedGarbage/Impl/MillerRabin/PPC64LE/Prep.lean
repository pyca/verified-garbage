module

public import VerifiedGarbage.Impl.MillerRabin.PPC64LE.Round

/-!
# Miller–Rabin's exponent on PPC64LE

`expSetup`, in the round's working space (array 0 at `r10`, the arrays'
size in `r29`, `2 w` in `r11`): for the odd candidate `c` in array 0 and
`c − 1 = m 2^a` (`m` odd), the exponent `E = (c − 1) / 2^σ` into array 27,
`σ ∈ [1, 4]` with `σ ≡ a (mod 4)`, and after its `w` words the lowest set
bit `l = 2^(a mod 64)` of `c − 1`'s lowest nonzero word, as
`Proof.MillerRabin.Round.Prepared` requires (the algorithm of AArch64's,
`Impl/MillerRabin/AArch64/Core.lean`):

* `lowWord`: `v |= x & mask (v = 0)` over the words `x` of `c − 1` (`c`'s,
  bit 0 of the first flipped), from the bottom: `v` is the lowest nonzero one;
* `lowBit`: `l = v & −v`, after the words of array 27;
* `E := c / 2` (`halfPass`), then halved again under the masks of `σ > 1`,
  `σ > 2` and `σ > 3`, those of `l & K ≠ 0` for the round's constants `K`.

Nothing branches on the candidate: the loops count `w`. It writes `r0`,
`r3`–`r7`, `r9` and `r14`–`r17`.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.PPC64LE

open VG VG.PPC64LE VG.Impl.Bignum VG.Impl.Bignum.PPC64LE
open VG.Impl.Bignum.PPC64LE.PublicChecked (base)

/-- `r5 :=` all ones if `r3 = 0`, else 0: `t = (r3 >> 1) | (r3 & 1)` is
below `2^63`, zero exactly when `r3` is, and `t − 1`'s sign bit is set
exactly then. -/
def zeroMask : List Instr :=
  [.lsr .d .r5 .r3 1, .li .r0 1, .logic .and .r0 .r3 .r0, .logic .or .r5 .r5 .r0, .subi .r5 .r5 1,
    .lsr .d .r5 .r5 63, .li .r0 0, .sub .r5 .r0 .r5]

/-- `r6 :=` the lowest nonzero word of `c − 1`. -/
def lowWord : Prog isa :=
  .seq (.block (base .r14 0 ++ [.lsr .d .r17 .r11 1, .li .r6 0, .li .r4 1]))
    (countLoop .r17 ([.load .d .r7 .r14 0, .logic .xor .r7 .r7 .r4, .li .r4 0, .addi .r3 .r6 0] ++ zeroMask ++
      [.logic .and .r7 .r7 .r5, .logic .or .r6 .r6 .r7, .addi .r14 .r14 8]))

/-- `r14 :=` the address of the word after array 27's `w` words. -/
def markerAddr : List Instr := base .r14 aE ++ [.lsl .r7 .r11 2, .add .r14 .r14 .r7]

/-- `l := v & −v` there. -/
def lowBit : List Instr := [.li .r7 0, .sub .r7 .r7 .r6, .logic .and .r6 .r6 .r7] ++ markerAddr ++
  [.store .d .r6 .r14 0]

/-- `[r16] := r9 ? [r15] / 2 : [r15]` over `w` words, in place when
`r16 = r15`: each word is written once the next is read. -/
def halfPass : Prog isa :=
  .seq (.block [.load .d .r5 .r15 0, .addi .r15 .r15 8, .lsr .d .r17 .r11 1, .subi .r17 .r17 1])
    (.seq (countLoop .r17 [.load .d .r3 .r15 0, .lsl .r4 .r3 63, .lsr .d .r6 .r5 1, .logic .or .r6 .r6 .r4,
        .logic .xor .r6 .r6 .r5, .logic .and .r6 .r6 .r9, .logic .xor .r6 .r6 .r5, .store .d .r6 .r16 0,
        .addi .r15 .r15 8, .addi .r16 .r16 8, .addi .r5 .r3 0])
      (.block [.lsr .d .r6 .r5 1, .logic .xor .r6 .r6 .r5, .logic .and .r6 .r6 .r9, .logic .xor .r6 .r6 .r5,
        .store .d .r6 .r16 0]))

/-- Array 27 halved in place under the mask of `σ > j`: `l & K ≠ 0`. -/
def halfCond (j : Nat) : Prog isa :=
  .seq (.block (markerAddr ++ [.load .d .r3 .r14 0] ++ repeat16 (sigK j) ++ [.logic .and .r3 .r3 .r4] ++
      zeroMask ++ [.li .r9 0, .subi .r9 .r9 1, .logic .xor .r9 .r9 .r5] ++ base .r15 aE ++ base .r16 aE))
    halfPass

/-- `E` and `l`. -/
def expSetup : Prog isa :=
  .seq lowWord (.seq (.block (lowBit ++ [.li .r9 0, .subi .r9 .r9 1] ++ base .r15 0 ++ base .r16 aE))
    (.seq halfPass (.seq (halfCond 1) (.seq (halfCond 2) (halfCond 3)))))

end VG.Impl.MillerRabin.PPC64LE
