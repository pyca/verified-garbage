module

public import VerifiedGarbage.TCB.RISCV64.Isa
public import VerifiedGarbage.Impl.Bignum.Layout

/-!
# Montgomery multiplication on RISC-V

The arithmetic of `[o] = [a] [b] R⁻¹ mod m` for `R = 2^(64 w)`, on numbers of
`w` words of 64 bits, least significant first, in the working space of
`Impl/Bignum/Layout.lean`: the modulus `m` at `a7`, the accumulator `T`
(`w + 1` words) at `a5` and a temporary (`w` words) at `a6`, with `o`, `a`
and `b` at `a2`, `a3` and `a4`, `w` in `t0` and `-m⁻¹ mod 2⁶⁴` in `t1`.

The multiplication is finely integrated operand scanning (FIOS) in radix
`2⁶⁴`, as on PPC64LE (`Impl/Bignum/PPC64LE/MontMul.lean`), with the carries
out of each addition by `sltu` (the sum is below an operand exactly when it
wrapped). For each word `aᵢ` of `a`, one pass over `T`, `b` and `m` computes
`T := (T + aᵢ b + u m) / 2⁶⁴`:

* word 0: `s₀ = t₀ + aᵢ b₀ mod 2⁶⁴` and the first carry `c`, the high word
  of `t₀ + aᵢ b₀`; `u = s₀ (-m⁻¹) mod 2⁶⁴`, so that `s₀ + u m₀` is a multiple
  of `2⁶⁴`, and the second carry `d = (s₀ + u m₀) / 2⁶⁴`;
* words `j = 1` to `w - 1`: `x = tⱼ + aᵢ bⱼ + c` and `y = x mod 2⁶⁴ + u mⱼ +
  d`, each below `2¹²⁸`, `c` and `d` their high words and the low word of `y`
  stored at word `j - 1`; `(w - 1) mod 4` words one at a time, then the
  others four at a time;
* word `w`: `t_w + c + d`, stored at words `w - 1` and `w`.

Each high word of a product is at most `2⁶⁴ - 2`, so adding a carry bit to
it does not wrap.

After the `w` rounds, `T < 2 m` and `T 2^(64 w) ≡ a b (mod m)`. Then `T - m`
is computed into the temporary word by word, the borrow a bit (`sltu`), and
the borrow out of the top word `t_w` selects `T` or `T - m` with a mask.

Every loop counts a register down from a public count (`w + 1`, `w`, `(w -
1) mod 4`, `(w - 1) / 4`), and every address is a base plus a constant, the
bases advanced by 8 per word, so only the bases and `w` affect timing.

Registers: in the rounds, `a1` the rounds left, `t3`, `t4`, `a0` the
pointers into the accumulator, `b` and `m`, `t5` the words (or groups of
four) left, `t6` `aᵢ`, `t2` `u`, `s0` and `s1` the carries `c` and `d`,
`s2`, `s3` temporaries and `s4` the carry bit of an addition; in the final
subtraction, `t3`, `t4`, `a0` the pointers, `t5` the words left, `s4` the
borrow, then the mask. The code writes `a0`, `a1`, `a3`, `t2`–`t6` and
`s0`–`s4`, and the memory of `[o]`, the accumulator and the temporary.
-/

@[expose] public section

namespace VG.Impl.Bignum.RISCV64

open VG.RISCV64 VG.Impl.Bignum

/-! ## Loops -/

/-- `do body; cnt -= 1 while cnt ≠ 0`, for `cnt` at least 1. -/
def countLoop (cnt : Reg) (body : List Instr) : Prog isa :=
  .loop (.block (body ++ ([.addi cnt cnt (-1)] : List Instr))) (.nonzero cnt)

/-- `if t5 ≠ 0` then `t5` times `body`. -/
def countLoop? (body : List Instr) : Prog isa :=
  .ite (.zero .t5) (.block []) (countLoop .t5 body)

/-- The accumulator's first `w + 1` words := 0, and the rounds' count `w`
into `a1`. -/
def zeroAcc : Prog isa :=
  .seq (.block [.addi .a1 .t0 0, .addi .t3 .a5 0, .addi .t5 .t0 1, .li .s0 0])
    (countLoop .t5 [.store .d .s0 .t3 0, .addi .t3 .t3 8])

/-! ## A round -/

/-- The start of a round, for `aᵢ` at `a3` (advanced): `aᵢ` into `t6`;
`s₀ = t₀ + aᵢ b₀ mod 2⁶⁴` into `s2` and the high word of `t₀ + aᵢ b₀` (the
first carry, `c`) into `s0`; `u = s₀ (-m⁻¹) mod 2⁶⁴` into `t2`; `(s₀ + u m₀) /
2⁶⁴` (the second carry, `d`: the low word is 0) into `s1`; the pointers `t3`,
`t4`, `a0` at word 0 of `T`, `b` and `m`. -/
def fiosHead : List Instr :=
  [.load .d .t6 .a3 0, .addi .a3 .a3 8, .load .d .s3 .a4 0, .load .d .s2 .a5 0,
    .mul .s0 .t6 .s3, .mulhu .s3 .t6 .s3, .add .s2 .s2 .s0, .sltu .s4 .s2 .s0, .add .s0 .s3 .s4,
    .mul .t2 .s2 .t1,
    .load .d .s3 .a7 0, .mul .s1 .t2 .s3, .mulhu .s3 .t2 .s3, .add .s1 .s1 .s2, .sltu .s4 .s1 .s2,
    .add .s1 .s3 .s4,
    .addi .t3 .a5 0, .addi .t4 .a4 0, .addi .a0 .a7 0]

/-- Word `j` of a round, the pointers at word `j - 1` less `k`: `x = tⱼ + aᵢ
bⱼ + c` (the words at `t3 + k + 8` and `t4 + k + 8`), `c` := its high word
and `y = x mod 2⁶⁴ + u mⱼ + d` (`mⱼ` at `a0 + k + 8`), `d` := its high word,
and its low word stored at `t3 + k`: word `j - 1` of `(T + aᵢ b + u m) /
2⁶⁴`. -/
def fiosStep (k : Nat) : List Instr :=
  [.load .d .s2 .t3 (k + 8), .add .s0 .s0 .s2, .sltu .s4 .s0 .s2,
    .load .d .s3 .t4 (k + 8), .mul .s2 .t6 .s3, .mulhu .s3 .t6 .s3, .add .s3 .s3 .s4,
    .add .s2 .s2 .s0, .sltu .s4 .s2 .s0, .add .s0 .s3 .s4,
    .load .d .s3 .a0 (k + 8), .add .s1 .s1 .s2, .sltu .s4 .s1 .s2,
    .mul .s2 .t2 .s3, .mulhu .s3 .t2 .s3, .add .s3 .s3 .s4,
    .add .s2 .s2 .s1, .sltu .s4 .s2 .s1, .add .s1 .s3 .s4, .store .d .s2 .t3 k]

/-- `U` words of a round, and the pointers advanced past them. -/
def fiosGroup (U : Nat) : List Instr :=
  (List.range U).flatMap (fun k => fiosStep (8 * k)) ++
    [.addi .t3 .t3 ((8 * U : Nat) : Int), .addi .t4 .t4 ((8 * U : Nat) : Int), .addi .a0 .a0 ((8 * U : Nat) : Int)]

/-- The words of a round are done four at a time. -/
def unroll : Nat := 4

/-- `(w - 1) mod 4` into `t5`. -/
def fiosRem : List Instr := [.addi .t5 .t0 (-1), .logicImm .and .t5 .t5 3]

/-- `(w - 1) / 4` into `t5`. -/
def fiosQuot : List Instr := [.addi .t5 .t0 (-1), .shift .srl .d .t5 .t5 2]

/-- Word `w` (above `t3`, at word `w - 1`) plus both carries, stored at words
`w - 1` and `w`. -/
def fiosTop : List Instr :=
  [.load .d .s2 .t3 8, .add .s0 .s0 .s2, .sltu .s4 .s0 .s2, .add .s0 .s0 .s1, .sltu .s3 .s0 .s1,
    .add .s4 .s4 .s3, .store .d .s0 .t3 0, .store .d .s4 .t3 8]

/-- One round: `T := (T + aᵢ b + u m) / 2⁶⁴`, finely integrated (FIOS): words
`1` to `w - 1` one at a time (`(w - 1) mod 4` of them), then four at a
time. -/
def round : Prog isa :=
  .seq (.block (fiosHead ++ fiosRem))
    (.seq (countLoop? (fiosGroup 1)) (.seq (.block fiosQuot) (.seq (countLoop? (fiosGroup unroll))
      (.block fiosTop))))

/-- The `w` rounds, counted by `a1`. -/
def rounds : Prog isa :=
  .loop (.seq round (.block [.addi .a1 .a1 (-1)])) (.nonzero .a1)

/-! ## The final subtraction -/

/-- `[tmp] = T - m` over `w` words, the borrow in `s4`, then `s4` := all
ones if `T < m` (the top word `t_w` is below the borrow), else 0. -/
def subMod64 : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t4 .a6 0, .addi .a0 .a7 0, .addi .t5 .t0 0, .li .s4 0])
    (.seq (countLoop .t5 [.load .d .s2 .t3 0, .load .d .s3 .a0 0, .sltu .s0 .s2 .s3,
        .sub .s2 .s2 .s3, .sltu .s1 .s2 .s4, .sub .s2 .s2 .s4, .logic .or .s4 .s0 .s1,
        .store .d .s2 .t4 0, .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8])
      (.block [.load .d .s2 .t3 0, .sltu .s0 .s2 .s4, .li .s1 0, .sub .s4 .s1 .s0]))

/-- `[o] = mask ? T : [tmp]`, word by word, the mask in `s4`. -/
def selectAcc64 : Prog isa :=
  .seq (.block [.addi .t3 .a5 0, .addi .t4 .a6 0, .addi .a0 .a2 0, .addi .t5 .t0 0])
    (countLoop .t5 [.load .d .s2 .t4 0, .load .d .s3 .t3 0, .logic .xor .s3 .s3 .s2,
      .logic .and .s3 .s3 .s4, .logic .xor .s3 .s3 .s2, .store .d .s3 .a0 0,
      .addi .t3 .t3 8, .addi .t4 .t4 8, .addi .a0 .a0 8])

/-- `[o] = [a] [b] R⁻¹ mod m`, for `R = 2^(64 w)`, the bases in the
registers. -/
def tail : Prog isa := .seq zeroAcc (.seq rounds (.seq subMod64 selectAcc64))

end VG.Impl.Bignum.RISCV64
