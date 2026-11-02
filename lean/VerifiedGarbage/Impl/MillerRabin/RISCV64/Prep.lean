module

public import VerifiedGarbage.Impl.MillerRabin.RISCV64.Round

/-!
# Miller–Rabin's exponent on RISC-V

`expSetup`, in the round's registers (`a7` array 0's base, `s5` the arrays'
size, `t0` `w`), as on PPC64LE (`Impl/MillerRabin/PPC64LE/Prep.lean`): for
the odd candidate `c` in array 0 and `c − 1 = m 2^a` (`m` odd), the exponent
`E = (c − 1) / 2^σ` into array 27, `σ ∈ [1, 4]` with `σ ≡ a (mod 4)`, and
after its `w` words the lowest set bit `l = 2^(a mod 64)` of `c − 1`'s lowest
nonzero word, as `Proof.MillerRabin.Round.Prepared` requires:

* `lowWord`: `v |= x & mask (v = 0)` over the words `x` of `c − 1` (`c`'s,
  bit 0 of the first flipped), from the bottom: `v` is the lowest nonzero one;
* `lowBit`: `l = v & −v`, after the words of array 27;
* `E := c / 2` (`halfPass`), then halved again under the masks of `σ > 1`,
  `σ > 2` and `σ > 3`, those of `l & K ≠ 0` for the round's constants `K`.

Nothing branches on the candidate: the loops count `w`. It writes `t2`–`t6`
and `s0`–`s4`.
-/

@[expose] public section

namespace VG.Impl.MillerRabin.RISCV64

open VG.RISCV64 VG.Impl.Bignum VG.Impl.Bignum.RISCV64
open VG.Impl.Bignum.RISCV64.PublicChecked (base)

/-- `s0 :=` the lowest nonzero word of `c − 1`, `s1` the bit flipped (1 for
the first word, then 0) and `s2` a word. -/
def lowWord : Prog isa :=
  .seq (.block (base .t3 0 ++ [.addi .t5 .t0 0, .li .s0 0, .li .s1 1]))
    (countLoop .t5 [.load .d .s2 .t3 0, .logic .xor .s2 .s2 .s1, .li .s1 0, .li .t2 0, .sltu .t2 .t2 .s0,
      .addi .t2 .t2 (-1), .logic .and .s2 .s2 .t2, .logic .or .s0 .s0 .s2, .addi .t3 .t3 8])

/-- `rd :=` the address of the word after array 27's `w` words. -/
def markerAddr (rd : Reg) : List Instr := base rd aE ++ [.shift .sll .d .t2 .t0 3, .add rd rd .t2]

/-- `l := v & −v` there. -/
def lowBit : List Instr := [.li .t2 0, .sub .t2 .t2 .s0, .logic .and .s0 .s0 .t2] ++ markerAddr .t3 ++
  [.store .d .s0 .t3 0]

/-- `[t4] := s3 ? [t3] / 2 : [t3]` over `w` words, in place when `t4 = t3`:
each word is written once the next is read. -/
def halfPass : Prog isa :=
  .seq (.block [.load .d .s0 .t3 0, .addi .t3 .t3 8, .addi .t5 .t0 (-1)])
    (.seq (countLoop .t5 [.load .d .s1 .t3 0, .shift .sll .d .s2 .s1 63, .shift .srl .d .s4 .s0 1,
        .logic .or .s4 .s4 .s2, .logic .xor .s4 .s4 .s0, .logic .and .s4 .s4 .s3, .logic .xor .s4 .s4 .s0,
        .store .d .s4 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .s0 .s1 0])
      (.block [.shift .srl .d .s4 .s0 1, .logic .xor .s4 .s4 .s0, .logic .and .s4 .s4 .s3,
        .logic .xor .s4 .s4 .s0, .store .d .s4 .t4 0]))

/-- Array 27 halved in place under the mask of `σ > j`: `l & K ≠ 0`. -/
def halfCond (j : Nat) : Prog isa :=
  .seq (.block (markerAddr .t3 ++ [.load .d .t3 .t3 0] ++ repeat16 .t4 .t5 (sigK j) ++
      [.logic .and .t3 .t3 .t4, .li .t2 0, .sltu .s3 .t2 .t3, .sub .s3 .t2 .s3] ++ base .t3 aE ++ base .t4 aE))
    halfPass

/-- `E` and `l`. -/
def expSetup : Prog isa :=
  .seq lowWord (.seq (.block (lowBit ++ [.li .s3 (-1)] ++ base .t3 0 ++ base .t4 aE))
    (.seq halfPass (.seq (halfCond 1) (.seq (halfCond 2) (halfCond 3)))))

end VG.Impl.MillerRabin.RISCV64
