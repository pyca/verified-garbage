module

public import VerifiedGarbage.Impl.Bignum.RISCV64.MontMul

/-!
# Montgomery squaring on RISC-V

`sqrTail`: `[o] = [a]² R⁻¹ mod m` for `R = 2^(64 w)`, on numbers of `w`
words of 64 bits, least significant first, in the working space of
`Impl/Bignum/Layout.lean`, with `MontMul.lean`'s `tail`'s registers: `o` at
`a2`, `a` at `a3`, `m` at `a7`, `w` in `t0` and `-m⁻¹ mod 2⁶⁴` in `t1`; the
product `T`, `2 w + 2` words, at `a5` (two adjacent arrays of the layout),
and the temporary of the final subtraction at `a6`.

A square's cross products `aᵢ aⱼ` (`i < j`) are each its double, so the
product is computed as the sum of the cross products once, doubled, plus the
squares of the words, with about half as many multiplications as `tail`'s
`a b`; the Montgomery reduction then takes as many as `tail`'s:

* `zeroT`: `T := 0`;
* `cross`: for `i = 0` to `w - 2`, `T += aᵢ (aᵢ₊₁ … a_{w-1}) 2^(64 (2 i + 1))`,
  the row's words added from word `2 i + 1` on, its carry stored at word
  `i + w` (which no earlier row reached);
* `diag`: `T := 2 T + Σ aᵢ² 2^(128 i)`, two words at a time, the bit shifted
  out of each pair (`t2`) and the carry (`s1`) into the next;
* `reduce`: for `i = 0` to `w - 1`, `u = tᵢ (-m⁻¹) mod 2⁶⁴` and `T += u m
  2^(64 i)`, which clears word `i`; the row's carry, and the carry out of
  word `i + w` left by the row before (`a1`), are added into word `i + w`;
* `finish`: the last carry stored at word `2 w`, then `T / R` (words `w` to
  `2 w`, below `2 m`) reduced into `[o]` by `MontMul.lean`'s `subMod64` and
  `selectAcc64`, with `a5` at word `w` meanwhile.

A step of a row (`sqrMac`) adds the product `x yⱼ`, the word `tⱼ` and the
carry word `s1`, in that order: the sum is below `2¹²⁸`, its low word stored
and its high word the next carry. The rows are unrolled by eight, the rest of
a row one word at a time (`macRun`).

Every multiplication is `mul` or `mulhu`, every loop counts a register down
from a public count (`w`, `w - 1 - i`, `2 w + 2`), and every address is a
base plus a constant: only the bases and `w` affect timing.

Registers: `t3` a row's pointer (into `a` in `cross`, into `T` in `diag` and
`reduce`), `t2` the start of a row in `T` (`cross`) or the rows left
(`reduce`) or the shifted-out bit (`diag`), `a1` the rows left (`cross`) or
the carry out of word `i + w` (`reduce`); in a row, `t4` and `a0` the
pointers into `T` and the operand, `t5` and `t6` the groups of eight and the
single words left, `s0` the multiplier, `s1` the carry, `s2`–`s4`
temporaries. The code writes `a0`, `a1`, `t2`–`t6` and `s0`–`s4`, and `a5`,
which it restores, and the memory of `T`, the temporary and `[o]`.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64

open VG.RISCV64 VG.Impl.Bignum

/-- `if r ≠ 0` then `r` times `body`. -/
def countLoopR? (r : Reg) (body : List Instr) : Prog isa :=
  .ite (.zero r) (.block []) (countLoop r body)

/-- `T := 0`: the `2 w + 2` words at `a5`. -/
def zeroT : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .add .t5 .t0 .t0, .addi .t5 .t5 2, .li .s0 0])
    (countLoop .t5 [.store .d .s0 .t3 0, .addi .t3 .t3 8])

/-- A step of a row, the pointers at its word less `k`: `x = tⱼ + s0 yⱼ + c`
(`tⱼ` at `t4 + k`, `yⱼ` at `a0 + k`, `c` in `s1`), its low word stored at
`t4 + k` and its high word the carry `s1`. `tⱼ` is added into the product's
low word first and the carry `c` last, each addition's carry into the high
word: three operations on each carry chain. -/
def sqrMac (k : Nat) : List Instr :=
  [.load .d .s4 .t4 k, .load .d .s2 .a0 k, .mul .s3 .s0 .s2, .mulhu .s2 .s0 .s2,
    .add .s3 .s3 .s4, .sltu .s4 .s3 .s4, .add .s2 .s2 .s4,
    .add .s3 .s3 .s1, .sltu .s4 .s3 .s1, .add .s1 .s2 .s4, .store .d .s3 .t4 k]

/-- `U` steps of a row, and the pointers advanced past them. -/
def macGroup (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => sqrMac (8 * k)) ++
    [.addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- A row of `t5` steps: groups of eight, then the rest one at a time. -/
def macRun : Prog isa :=
  .seq (.block [.logicImm .and .t6 .t5 7, .shift .srl .d .t5 .t5 3])
    (.seq (countLoopR? .t5 (macGroup 8)) (countLoopR? .t6 (macGroup 1)))

/-- The cross products: for each word `aᵢ` but the last (`t3`, advanced),
`T += aᵢ (aᵢ₊₁ …) 2^(64 (2 i + 1))` from word `2 i + 1` (`t2`, advanced by
two words), `w - 1 - i` steps (`a1`, counted down), its carry stored above. -/
def cross : Prog isa :=
  .seq (.block [.addi .t3 .a3 0, .addi .a1 .t0 (-1), .addi .t2 .a5 8])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .li .s1 0, .addi .a0 .t3 8, .addi .t4 .t2 0,
        .addi .t5 .a1 0])
      (.seq macRun (.block [.store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 16,
        .addi .a1 .a1 (-1)])))
      (.nonzero .a1))

/-- A step of `diag`: words `2 i` and `2 i + 1` of `T` (at `t3`) doubled, with
the bit shifted out of the pair before (`t2`) and the carry (`s1`), plus
`aᵢ²` (`aᵢ` at `a0`); the bit shifted out into `t2`, the carry into `s1`. -/
def diagStep : List Instr :=
  [.load .d .s2 .t3 0, .load .d .s3 .t3 8, .shift .srl .d .s4 .s2 63, .shift .sll .d .s2 .s2 1,
    .add .s2 .s2 .t2, .shift .srl .d .t2 .s3 63, .shift .sll .d .s3 .s3 1, .add .s3 .s3 .s4,
    .load .d .s4 .a0 0, .add .s1 .s1 .s2, .sltu .s2 .s1 .s2, .mul .s0 .s4 .s4, .mulhu .s4 .s4 .s4,
    .add .s4 .s4 .s2, .add .s0 .s0 .s1, .sltu .s2 .s0 .s1, .add .s4 .s4 .s2, .add .s3 .s3 .s4,
    .sltu .s1 .s3 .s4, .store .d .s0 .t3 0, .store .d .s3 .t3 8, .addi .t3 .t3 16, .addi .a0 .a0 8]

/-- `T := 2 T + Σ aᵢ² 2^(128 i)`, `w` steps. -/
def diag : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .a0 .a3 0, .addi .t5 .t0 0, .li .t2 0, .li .s1 0])
    (countLoop .t5 diagStep)

/-- The end of a row of the reduction: the row's carry (`s1`) and the carry
`a1` out of the word before added into word `i + w` (at `t4`), the carry
out into `a1`; the row's pointer `t3` advanced and the rows left `t2`
counted down. -/
def redTop : List Instr :=
  [.load .d .s2 .t4 0, .add .s1 .s1 .s2, .sltu .s3 .s1 .s2, .add .s1 .s1 .a1, .sltu .s2 .s1 .a1,
    .add .a1 .s3 .s2, .store .d .s1 .t4 0, .addi .t3 .t3 8, .addi .t2 .t2 (-1)]

/-- The Montgomery reduction of `T`: for each word `tᵢ` (`t3`, advanced),
`u = tᵢ (-m⁻¹) mod 2⁶⁴` into `s0` and `T += u m 2^(64 i)` (`w` steps), then
`redTop`; `w` rows (`t2`). -/
def reduce : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t2 .t0 0, .li .a1 0])
    (.loop (.seq (.block [.load .d .s0 .t3 0, .mul .s0 .s0 .t1, .li .s1 0, .addi .a0 .a7 0,
        .addi .t4 .t3 0, .addi .t5 .t0 0])
      (.seq macRun (.block redTop)))
      (.nonzero .t2))

/-- The last carry at word `2 w`, `a5` at word `w`. -/
def finishPre : List Instr :=
  [.shift .sll .d .t3 .t0 3, .add .a5 .a5 .t3, .add .t4 .a5 .t3, .store .d .a1 .t4 0]

/-- `a5` back at word 0. -/
def finishPost : List Instr := [.shift .sll .d .t3 .t0 3, .sub .a5 .a5 .t3]

/-- `[o] = [a]² R⁻¹ mod m`, for `R = 2^(64 w)` and `w ≥ 2`, the bases in the
registers. -/
def sqrTail : Prog isa :=
  .seq zeroT (.seq cross (.seq diag (.seq reduce
    (.seq (.block finishPre) (.seq subMod64 (.seq selectAcc64 (.block finishPost)))))))

end VG.Impl.Bignum.RISCV64
